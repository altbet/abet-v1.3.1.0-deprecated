// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Copyright (c) 2014-2015 The Dash developers
// Copyright (c) 2015-2017 The PIVX developers
// Copyright (c) 2018 altbet.io
//  
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "main.h"

#include "addrman.h"
#include "alert.h"
#include "chainparams.h"
#include "checkpoints.h"
#include "checkqueue.h"
#include "init.h"
#include "kernel.h"
#include "masternode-budget.h"
#include "masternode-payments.h"
#include "masternodeman.h"
#include "merkleblock.h"
#include "net.h"
#include "obfuscation.h"
#include "pow.h"
#include "spork.h"
#include "swifttx.h"
#include "txdb.h"
#include "txmempool.h"
#include "ui_interface.h"
#include "util.h"
#include "utilmoneystr.h"

#include <sstream>

#include <boost/algorithm/string/replace.hpp>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/thread.hpp>

using namespace boost;
using namespace std;

#if defined(NDEBUG)
#error "Altbet cannot be compiled without assertions."
#endif

/**
 * Global state
 */

CCriticalSection cs_main;

BlockMap mapBlockIndex;
map<uint256, uint256> mapProofOfStake;
set<pair<COutPoint, unsigned int> > setStakeSeen;

// maps any spent outputs in the past maxreorgdepth blocks to the height it was spent
// this means for incoming blocks, we can check that their stake output was not spent before
// the incoming block tried to use it as a staking input. We can also prevent block spam
// attacks because then we can check that either the staking input is available in the current
// active chain, or the staking input was spent in the past 100 blocks after the height
// of the incoming block.
map<COutPoint, int> mapStakeSpent;

map<unsigned int, unsigned int> mapHashedBlocks;
CChain chainActive;
CBlockIndex* pindexBestHeader = NULL;
int64_t nTimeBestReceived = 0;
CWaitableCriticalSection csBestBlock;
CConditionVariable cvBlockChange;
int nScriptCheckThreads = 0;
bool fImporting = false;
bool fReindex = false;
bool fTxIndex = true;
bool fIsBareMultisigStd = true;
bool fCheckBlockIndex = false;
unsigned int nCoinCacheSize = 5000;
bool fAlerts = DEFAULT_ALERTS;

unsigned int nStakeMinAge = 60 * 60;
int64_t nReserveBalance = 0;

/** Fees smaller than this (in duffs) are considered zero fee (for relaying and mining)
 * We are ~100 times smaller then bitcoin now (2015-06-23), set minRelayTxFee only 10 times higher
 * so it's still 10 times lower comparing to bitcoin.
 */
CFeeRate minRelayTxFee = CFeeRate(10000);

CTxMemPool mempool(::minRelayTxFee);

struct COrphanTx {
    CTransaction tx;
    NodeId fromPeer;
};
map<uint256, COrphanTx> mapOrphanTransactions;
map<uint256, set<uint256> > mapOrphanTransactionsByPrev;
map<uint256, int64_t> mapRejectedBlocks;


void EraseOrphansFor(NodeId peer);

static void CheckBlockIndex();

/** Constant stuff for coinbase transactions we create: */
CScript COINBASE_FLAGS;

const string strMessageMagic = "DarkNet Signed Message:\n";

// Internal stuff
namespace
{
struct CBlockIndexWorkComparator {
    bool operator()(CBlockIndex* pa, CBlockIndex* pb) const
    {
        // First sort by most total work, ...
        if (pa->nChainWork > pb->nChainWork) return false;
        if (pa->nChainWork < pb->nChainWork) return true;

        // ... then by earliest time received, ...
        if (pa->nSequenceId < pb->nSequenceId) return false;
        if (pa->nSequenceId > pb->nSequenceId) return true;

        // Use pointer address as tie breaker (should only happen with blocks
        // loaded from disk, as those all have id 0).
        if (pa < pb) return false;
        if (pa > pb) return true;

        // Identical blocks.
        return false;
    }
};

CBlockIndex* pindexBestInvalid;

/**
     * The set of all CBlockIndex entries with BLOCK_VALID_TRANSACTIONS (for itself and all ancestors) and
     * as good as our current tip or better. Entries may be failed, though.
     */
set<CBlockIndex*, CBlockIndexWorkComparator> setBlockIndexCandidates;
/** Number of nodes with fSyncStarted. */
int nSyncStarted = 0;
/** All pairs A->B, where A (or one if its ancestors) misses transactions, but B has transactions. */
multimap<CBlockIndex*, CBlockIndex*> mapBlocksUnlinked;

CCriticalSection cs_LastBlockFile;
std::vector<CBlockFileInfo> vinfoBlockFile;
int nLastBlockFile = 0;

/**
     * Every received block is assigned a unique and increasing identifier, so we
     * know which one to give priority in case of a fork.
     */
CCriticalSection cs_nBlockSequenceId;
/** Blocks loaded from disk are assigned id 0, so start the counter at 1. */
uint32_t nBlockSequenceId = 1;

/**
     * Sources of received blocks, to be able to send them reject messages or ban
     * them, if processing happens afterwards. Protected by cs_main.
     */
map<uint256, NodeId> mapBlockSource;

/** Blocks that are in flight, and that are in the queue to be downloaded. Protected by cs_main. */
struct QueuedBlock {
    uint256 hash;
    CBlockIndex* pindex;        //! Optional.
    int64_t nTime;              //! Time of "getdata" request in microseconds.
    int nValidatedQueuedBefore; //! Number of blocks queued with validated headers (globally) at the time this one is requested.
    bool fValidatedHeaders;     //! Whether this block has validated headers at the time of request.
};
map<uint256, pair<NodeId, list<QueuedBlock>::iterator> > mapBlocksInFlight;

/** Number of blocks in flight with validated headers. */
int nQueuedValidatedHeaders = 0;

/** Number of preferable block download peers. */
int nPreferredDownload = 0;

/** Dirty block index entries. */
set<CBlockIndex*> setDirtyBlockIndex;

/** Dirty block file entries. */
set<int> setDirtyFileInfo;
} // anon namespace

//////////////////////////////////////////////////////////////////////////////
//
// dispatching functions
//

// These functions dispatch to one or all registered wallets

namespace
{
struct CMainSignals {
    /** Notifies listeners of updated transaction data (transaction, and optionally the block it is found in. */
    boost::signals2::signal<void(const CTransaction&, const CBlock*)> SyncTransaction;
    /** Notifies listeners of an erased transaction (currently disabled, requires transaction replacement). */
// XX42    boost::signals2::signal<void(const uint256&)> EraseTransaction;
    /** Notifies listeners of an updated transaction without new data (for now: a coinbase potentially becoming visible). */
    boost::signals2::signal<void(const uint256&)> UpdatedTransaction;
    /** Notifies listeners of a new active block chain. */
    boost::signals2::signal<void(const CBlockLocator&)> SetBestChain;
    /** Notifies listeners about an inventory item being seen on the network. */
    boost::signals2::signal<void(const uint256&)> Inventory;
    /** Tells listeners to broadcast their data. */
    boost::signals2::signal<void()> Broadcast;
    /** Notifies listeners of a block validation result */
    boost::signals2::signal<void(const CBlock&, const CValidationState&)> BlockChecked;
} g_signals;

} // anon namespace

void RegisterValidationInterface(CValidationInterface* pwalletIn)
{
    g_signals.SyncTransaction.connect(boost::bind(&CValidationInterface::SyncTransaction, pwalletIn, _1, _2));
// XX42 g_signals.EraseTransaction.connect(boost::bind(&CValidationInterface::EraseFromWallet, pwalletIn, _1));
    g_signals.UpdatedTransaction.connect(boost::bind(&CValidationInterface::UpdatedTransaction, pwalletIn, _1));
    g_signals.SetBestChain.connect(boost::bind(&CValidationInterface::SetBestChain, pwalletIn, _1));
    g_signals.Inventory.connect(boost::bind(&CValidationInterface::Inventory, pwalletIn, _1));
    g_signals.Broadcast.connect(boost::bind(&CValidationInterface::ResendWalletTransactions, pwalletIn));
    g_signals.BlockChecked.connect(boost::bind(&CValidationInterface::BlockChecked, pwalletIn, _1, _2));
}

void UnregisterValidationInterface(CValidationInterface* pwalletIn)
{
    g_signals.BlockChecked.disconnect(boost::bind(&CValidationInterface::BlockChecked, pwalletIn, _1, _2));
    g_signals.Broadcast.disconnect(boost::bind(&CValidationInterface::ResendWalletTransactions, pwalletIn));
    g_signals.Inventory.disconnect(boost::bind(&CValidationInterface::Inventory, pwalletIn, _1));
    g_signals.SetBestChain.disconnect(boost::bind(&CValidationInterface::SetBestChain, pwalletIn, _1));
    g_signals.UpdatedTransaction.disconnect(boost::bind(&CValidationInterface::UpdatedTransaction, pwalletIn, _1));
// XX42    g_signals.EraseTransaction.disconnect(boost::bind(&CValidationInterface::EraseFromWallet, pwalletIn, _1));
    g_signals.SyncTransaction.disconnect(boost::bind(&CValidationInterface::SyncTransaction, pwalletIn, _1, _2));
}

void UnregisterAllValidationInterfaces()
{
    g_signals.BlockChecked.disconnect_all_slots();
    g_signals.Broadcast.disconnect_all_slots();
    g_signals.Inventory.disconnect_all_slots();
    g_signals.SetBestChain.disconnect_all_slots();
    g_signals.UpdatedTransaction.disconnect_all_slots();
// XX42    g_signals.EraseTransaction.disconnect_all_slots();
    g_signals.SyncTransaction.disconnect_all_slots();
}

void SyncWithWallets(const CTransaction& tx, const CBlock* pblock)
{
    g_signals.SyncTransaction(tx, pblock);
}

//////////////////////////////////////////////////////////////////////////////
//
// Registration of network node signals.
//

namespace
{
struct CBlockReject {
    unsigned char chRejectCode;
    string strRejectReason;
    uint256 hashBlock;
};

/**
 * Maintain validation-specific state about nodes, protected by cs_main, instead
 * by CNode's own locks. This simplifies asynchronous operation, where
 * processing of incoming data is done after the ProcessMessage call returns,
 * and we're no longer holding the node's locks.
 */
struct CNodeState {
    //! The peer's address
    CService address;
    //! Whether we have a fully established connection.
    bool fCurrentlyConnected;
    //! Accumulated misbehaviour score for this peer.
    int nMisbehavior;
    //! Whether this peer should be disconnected and banned (unless whitelisted).
    bool fShouldBan;
    //! String name of this peer (debugging/logging purposes).
    std::string name;
    //! List of asynchronously-determined block rejections to notify this peer about.
    std::vector<CBlockReject> rejects;
    //! The best known block we know this peer has announced.
    CBlockIndex* pindexBestKnownBlock;
    //! The hash of the last unknown block this peer has announced.
    uint256 hashLastUnknownBlock;
    //! The last full block we both have.
    CBlockIndex* pindexLastCommonBlock;
    //! Whether we've started headers synchronization with this peer.
    bool fSyncStarted;
    //! Since when we're stalling block download progress (in microseconds), or 0.
    int64_t nStallingSince;
    list<QueuedBlock> vBlocksInFlight;
    int nBlocksInFlight;
    //! Whether we consider this a preferred download peer.
    bool fPreferredDownload;

    CNodeState()
    {
        fCurrentlyConnected = false;
        nMisbehavior = 0;
        fShouldBan = false;
        pindexBestKnownBlock = NULL;
        hashLastUnknownBlock = uint256(0);
        pindexLastCommonBlock = NULL;
        fSyncStarted = false;
        nStallingSince = 0;
        nBlocksInFlight = 0;
        fPreferredDownload = false;
    }
};

/** Map maintaining per-node state. Requires cs_main. */
map<NodeId, CNodeState> mapNodeState;

// Requires cs_main.
CNodeState* State(NodeId pnode)
{
    map<NodeId, CNodeState>::iterator it = mapNodeState.find(pnode);
    if (it == mapNodeState.end())
        return NULL;
    return &it->second;
}

int GetHeight()
{
    while (true) {
        TRY_LOCK(cs_main, lockMain);
        if (!lockMain) {
            MilliSleep(50);
            continue;
        }
        return chainActive.Height();
    }
}

void UpdatePreferredDownload(CNode* node, CNodeState* state)
{
    nPreferredDownload -= state->fPreferredDownload;

    // Whether this node should be marked as a preferred download node.
    state->fPreferredDownload = (!node->fInbound || node->fWhitelisted) && !node->fOneShot && !node->fClient;

    nPreferredDownload += state->fPreferredDownload;
}

void InitializeNode(NodeId nodeid, const CNode* pnode)
{
    LOCK(cs_main);
    CNodeState& state = mapNodeState.insert(std::make_pair(nodeid, CNodeState())).first->second;
    state.name = pnode->addrName;
    state.address = pnode->addr;
}

void FinalizeNode(NodeId nodeid)
{
    LOCK(cs_main);
    CNodeState* state = State(nodeid);

    if (state->fSyncStarted)
        nSyncStarted--;

    if (state->nMisbehavior == 0 && state->fCurrentlyConnected) {
        AddressCurrentlyConnected(state->address);
    }

    BOOST_FOREACH (const QueuedBlock& entry, state->vBlocksInFlight)
        mapBlocksInFlight.erase(entry.hash);
    EraseOrphansFor(nodeid);
    nPreferredDownload -= state->fPreferredDownload;

    mapNodeState.erase(nodeid);
}

// Requires cs_main.
void MarkBlockAsReceived(const uint256& hash)
{
    map<uint256, pair<NodeId, list<QueuedBlock>::iterator> >::iterator itInFlight = mapBlocksInFlight.find(hash);
    if (itInFlight != mapBlocksInFlight.end()) {
        CNodeState* state = State(itInFlight->second.first);
        nQueuedValidatedHeaders -= itInFlight->second.second->fValidatedHeaders;
        state->vBlocksInFlight.erase(itInFlight->second.second);
        state->nBlocksInFlight--;
        state->nStallingSince = 0;
        mapBlocksInFlight.erase(itInFlight);
    }
}

// Requires cs_main.
void MarkBlockAsInFlight(NodeId nodeid, const uint256& hash, CBlockIndex* pindex = NULL)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    // Make sure it's not listed somewhere already.
    MarkBlockAsReceived(hash);

    QueuedBlock newentry = {hash, pindex, GetTimeMicros(), nQueuedValidatedHeaders, pindex != NULL};
    nQueuedValidatedHeaders += newentry.fValidatedHeaders;
    list<QueuedBlock>::iterator it = state->vBlocksInFlight.insert(state->vBlocksInFlight.end(), newentry);
    state->nBlocksInFlight++;
    mapBlocksInFlight[hash] = std::make_pair(nodeid, it);
}

/** Check whether the last unknown block a peer advertized is not yet known. */
void ProcessBlockAvailability(NodeId nodeid)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    if (state->hashLastUnknownBlock != 0) {
        BlockMap::iterator itOld = mapBlockIndex.find(state->hashLastUnknownBlock);
        if (itOld != mapBlockIndex.end() && itOld->second->nChainWork > 0) {
            if (state->pindexBestKnownBlock == NULL || itOld->second->nChainWork >= state->pindexBestKnownBlock->nChainWork)
                state->pindexBestKnownBlock = itOld->second;
            state->hashLastUnknownBlock = uint256(0);
        }
    }
}

/** Update tracking information about which blocks a peer is assumed to have. */
void UpdateBlockAvailability(NodeId nodeid, const uint256& hash)
{
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    ProcessBlockAvailability(nodeid);

    BlockMap::iterator it = mapBlockIndex.find(hash);
    if (it != mapBlockIndex.end() && it->second->nChainWork > 0) {
        // An actually better block was announced.
        if (state->pindexBestKnownBlock == NULL || it->second->nChainWork >= state->pindexBestKnownBlock->nChainWork)
            state->pindexBestKnownBlock = it->second;
    } else {
        // An unknown block was announced; just assume that the latest one is the best one.
        state->hashLastUnknownBlock = hash;
    }
}

/** Find the last common ancestor two blocks have.
 *  Both pa and pb must be non-NULL. */
CBlockIndex* LastCommonAncestor(CBlockIndex* pa, CBlockIndex* pb)
{
    if (pa->nHeight > pb->nHeight) {
        pa = pa->GetAncestor(pb->nHeight);
    } else if (pb->nHeight > pa->nHeight) {
        pb = pb->GetAncestor(pa->nHeight);
    }

    while (pa != pb && pa && pb) {
        pa = pa->pprev;
        pb = pb->pprev;
    }

    // Eventually all chain branches meet at the genesis block.
    assert(pa == pb);
    return pa;
}

/** Update pindexLastCommonBlock and add not-in-flight missing successors to vBlocks, until it has
 *  at most count entries. */
void FindNextBlocksToDownload(NodeId nodeid, unsigned int count, std::vector<CBlockIndex*>& vBlocks, NodeId& nodeStaller)
{
    if (count == 0)
        return;

    vBlocks.reserve(vBlocks.size() + count);
    CNodeState* state = State(nodeid);
    assert(state != NULL);

    // Make sure pindexBestKnownBlock is up to date, we'll need it.
    ProcessBlockAvailability(nodeid);

    if (state->pindexBestKnownBlock == NULL || state->pindexBestKnownBlock->nChainWork < chainActive.Tip()->nChainWork) {
        // This peer has nothing interesting.
        return;
    }

    if (state->pindexLastCommonBlock == NULL) {
        // Bootstrap quickly by guessing a parent of our best tip is the forking point.
        // Guessing wrong in either direction is not a problem.
        state->pindexLastCommonBlock = chainActive[std::min(state->pindexBestKnownBlock->nHeight, chainActive.Height())];
    }

    // If the peer reorganized, our previous pindexLastCommonBlock may not be an ancestor
    // of their current tip anymore. Go back enough to fix that.
    state->pindexLastCommonBlock = LastCommonAncestor(state->pindexLastCommonBlock, state->pindexBestKnownBlock);
    if (state->pindexLastCommonBlock == state->pindexBestKnownBlock)
        return;

    std::vector<CBlockIndex*> vToFetch;
    CBlockIndex* pindexWalk = state->pindexLastCommonBlock;
    // Never fetch further than the best block we know the peer has, or more than BLOCK_DOWNLOAD_WINDOW + 1 beyond the last
    // linked block we have in common with this peer. The +1 is so we can detect stalling, namely if we would be able to
    // download that next block if the window were 1 larger.
    int nWindowEnd = state->pindexLastCommonBlock->nHeight + BLOCK_DOWNLOAD_WINDOW;
    int nMaxHeight = std::min<int>(state->pindexBestKnownBlock->nHeight, nWindowEnd + 1);
    NodeId waitingfor = -1;
    while (pindexWalk->nHeight < nMaxHeight) {
        // Read up to 128 (or more, if more blocks than that are needed) successors of pindexWalk (towards
        // pindexBestKnownBlock) into vToFetch. We fetch 128, because CBlockIndex::GetAncestor may be as expensive
        // as iterating over ~100 CBlockIndex* entries anyway.
        int nToFetch = std::min(nMaxHeight - pindexWalk->nHeight, std::max<int>(count - vBlocks.size(), 128));
        vToFetch.resize(nToFetch);
        pindexWalk = state->pindexBestKnownBlock->GetAncestor(pindexWalk->nHeight + nToFetch);
        vToFetch[nToFetch - 1] = pindexWalk;
        for (unsigned int i = nToFetch - 1; i > 0; i--) {
            vToFetch[i - 1] = vToFetch[i]->pprev;
        }

        // Iterate over those blocks in vToFetch (in forward direction), adding the ones that
        // are not yet downloaded and not in flight to vBlocks. In the mean time, update
        // pindexLastCommonBlock as long as all ancestors are already downloaded.
        BOOST_FOREACH (CBlockIndex* pindex, vToFetch) {
            if (!pindex->IsValid(BLOCK_VALID_TREE)) {
                // We consider the chain that this peer is on invalid.
                return;
            }
            if (pindex->nStatus & BLOCK_HAVE_DATA) {
                if (pindex->nChainTx)
                    state->pindexLastCommonBlock = pindex;
            } else if (mapBlocksInFlight.count(pindex->GetBlockHash()) == 0) {
                // The block is not already downloaded, and not yet in flight.
                if (pindex->nHeight > nWindowEnd) {
                    // We reached the end of the window.
                    if (vBlocks.size() == 0 && waitingfor != nodeid) {
                        // We aren't able to fetch anything, but we would be if the download window was one larger.
                        nodeStaller = waitingfor;
                    }
                    return;
                }
                vBlocks.push_back(pindex);
                if (vBlocks.size() == count) {
                    return;
                }
            } else if (waitingfor == -1) {
                // This is the first already-in-flight block.
                waitingfor = mapBlocksInFlight[pindex->GetBlockHash()].first;
            }
        }
    }
}

} // anon namespace

bool GetNodeStateStats(NodeId nodeid, CNodeStateStats& stats)
{
    LOCK(cs_main);
    CNodeState* state = State(nodeid);
    if (state == NULL)
        return false;
    stats.nMisbehavior = state->nMisbehavior;
    stats.nSyncHeight = state->pindexBestKnownBlock ? state->pindexBestKnownBlock->nHeight : -1;
    stats.nCommonHeight = state->pindexLastCommonBlock ? state->pindexLastCommonBlock->nHeight : -1;
    BOOST_FOREACH (const QueuedBlock& queue, state->vBlocksInFlight) {
        if (queue.pindex)
            stats.vHeightInFlight.push_back(queue.pindex->nHeight);
    }
    return true;
}

void RegisterNodeSignals(CNodeSignals& nodeSignals)
{
    nodeSignals.GetHeight.connect(&GetHeight);
    nodeSignals.ProcessMessages.connect(&ProcessMessages);
    nodeSignals.SendMessages.connect(&SendMessages);
    nodeSignals.InitializeNode.connect(&InitializeNode);
    nodeSignals.FinalizeNode.connect(&FinalizeNode);
}

void UnregisterNodeSignals(CNodeSignals& nodeSignals)
{
    nodeSignals.GetHeight.disconnect(&GetHeight);
    nodeSignals.ProcessMessages.disconnect(&ProcessMessages);
    nodeSignals.SendMessages.disconnect(&SendMessages);
    nodeSignals.InitializeNode.disconnect(&InitializeNode);
    nodeSignals.FinalizeNode.disconnect(&FinalizeNode);
}

CBlockIndex* FindForkInGlobalIndex(const CChain& chain, const CBlockLocator& locator)
{
    // Find the first block the caller has in the main chain
    BOOST_FOREACH (const uint256& hash, locator.vHave) {
        BlockMap::iterator mi = mapBlockIndex.find(hash);
        if (mi != mapBlockIndex.end()) {
            CBlockIndex* pindex = (*mi).second;
            if (chain.Contains(pindex))
                return pindex;
        }
    }
    return chain.Genesis();
}

CCoinsViewCache* pcoinsTip = NULL;
CBlockTreeDB* pblocktree = NULL;

//////////////////////////////////////////////////////////////////////////////
//
// mapOrphanTransactions
//

bool AddOrphanTx(const CTransaction& tx, NodeId peer)
{
    uint256 hash = tx.GetHash();
    if (mapOrphanTransactions.count(hash))
        return false;

    // Ignore big transactions, to avoid a
    // send-big-orphans memory exhaustion attack. If a peer has a legitimate
    // large transaction with a missing parent then we assume
    // it will rebroadcast it later, after the parent transaction(s)
    // have been mined or received.
    // 10,000 orphans, each of which is at most 5,000 bytes big is
    // at most 500 megabytes of orphans:
    unsigned int sz = tx.GetSerializeSize(SER_NETWORK, CTransaction::CURRENT_VERSION);
    if (sz > 5000) {
        LogPrint("mempool", "ignoring large orphan tx (size: %u, hash: %s)\n", sz, hash.ToString());
        return false;
    }

    mapOrphanTransactions[hash].tx = tx;
    mapOrphanTransactions[hash].fromPeer = peer;
    BOOST_FOREACH (const CTxIn& txin, tx.vin)
        mapOrphanTransactionsByPrev[txin.prevout.hash].insert(hash);

    LogPrint("mempool", "stored orphan tx %s (mapsz %u prevsz %u)\n", hash.ToString(),
        mapOrphanTransactions.size(), mapOrphanTransactionsByPrev.size());
    return true;
}

void static EraseOrphanTx(uint256 hash)
{
    map<uint256, COrphanTx>::iterator it = mapOrphanTransactions.find(hash);
    if (it == mapOrphanTransactions.end())
        return;
    BOOST_FOREACH (const CTxIn& txin, it->second.tx.vin) {
        map<uint256, set<uint256> >::iterator itPrev = mapOrphanTransactionsByPrev.find(txin.prevout.hash);
        if (itPrev == mapOrphanTransactionsByPrev.end())
            continue;
        itPrev->second.erase(hash);
        if (itPrev->second.empty())
            mapOrphanTransactionsByPrev.erase(itPrev);
    }
    mapOrphanTransactions.erase(it);
}

void EraseOrphansFor(NodeId peer)
{
    int nErased = 0;
    map<uint256, COrphanTx>::iterator iter = mapOrphanTransactions.begin();
    while (iter != mapOrphanTransactions.end()) {
        map<uint256, COrphanTx>::iterator maybeErase = iter++; // increment to avoid iterator becoming invalid
        if (maybeErase->second.fromPeer == peer) {
            EraseOrphanTx(maybeErase->second.tx.GetHash());
            ++nErased;
        }
    }
    if (nErased > 0) LogPrint("mempool", "Erased %d orphan tx from peer %d\n", nErased, peer);
}


unsigned int LimitOrphanTxSize(unsigned int nMaxOrphans)
{
    unsigned int nEvicted = 0;
    while (mapOrphanTransactions.size() > nMaxOrphans) {
        // Evict a random orphan:
        uint256 randomhash = GetRandHash();
        map<uint256, COrphanTx>::iterator it = mapOrphanTransactions.lower_bound(randomhash);
        if (it == mapOrphanTransactions.end())
            it = mapOrphanTransactions.begin();
        EraseOrphanTx(it->first);
        ++nEvicted;
    }
    return nEvicted;
}

bool IsStandardTx(const CTransaction& tx, string& reason)
{
    AssertLockHeld(cs_main);
    if (tx.nVersion > CTransaction::CURRENT_VERSION || tx.nVersion < 1) {
        reason = "version";
        return false;
    }

    // Treat non-final transactions as non-standard to prevent a specific type
    // of double-spend attack, as well as DoS attacks. (if the transaction
    // can't be mined, the attacker isn't expending resources broadcasting it)
    // Basically we don't want to propagate transactions that can't be included in
    // the next block.
    //
    // However, IsFinalTx() is confusing... Without arguments, it uses
    // chainActive.Height() to evaluate nLockTime; when a block is accepted, chainActive.Height()
    // is set to the value of nHeight in the block. However, when IsFinalTx()
    // is called within CBlock::AcceptBlock(), the height of the block *being*
    // evaluated is what is used. Thus if we want to know if a transaction can
    // be part of the *next* block, we need to call IsFinalTx() with one more
    // than chainActive.Height().
    //
    // Timestamps on the other hand don't get any special treatment, because we
    // can't know what timestamp the next block will have, and there aren't
    // timestamp applications where it matters.
    if (!IsFinalTx(tx, chainActive.Height() + 1)) {
        reason = "non-final";
        return false;
    }

    // Extremely large transactions with lots of inputs can cost the network
    // almost as much to process as they cost the sender in fees, because
    // computing signature hashes is O(ninputs*txsize). Limiting transactions
    // to MAX_STANDARD_TX_SIZE mitigates CPU exhaustion attacks.
    unsigned int sz = tx.GetSerializeSize(SER_NETWORK, CTransaction::CURRENT_VERSION);
    if (sz >= MAX_STANDARD_TX_SIZE) {
        reason = "tx-size";
        return false;
    }

    BOOST_FOREACH (const CTxIn& txin, tx.vin) {
        // Biggest 'standard' txin is a 15-of-15 P2SH multisig with compressed
        // keys. (remember the 520 byte limit on redeemScript size) That works
        // out to a (15*(33+1))+3=513 byte redeemScript, 513+1+15*(73+1)+3=1627
        // bytes of scriptSig, which we round off to 1650 bytes for some minor
        // future-proofing. That's also enough to spend a 20-of-20
        // CHECKMULTISIG scriptPubKey, though such a scriptPubKey is not
        // considered standard)
        if (txin.scriptSig.size() > 1650) {
            reason = "scriptsig-size";
            return false;
        }
        if (!txin.scriptSig.IsPushOnly()) {
            reason = "scriptsig-not-pushonly";
            return false;
        }
    }

    unsigned int nDataOut = 0;
    txnouttype whichType;
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        if (!::IsStandard(txout.scriptPubKey, whichType)) {
            reason = "scriptpubkey";
            return false;
        }

        if (whichType == TX_NULL_DATA)
            nDataOut++;
        else if ((whichType == TX_MULTISIG) && (!fIsBareMultisigStd)) {
            reason = "bare-multisig";
            return false;
        } else if (txout.IsDust(::minRelayTxFee)) {
            reason = "dust";
            return false;
        }
    }

    // only one OP_RETURN txout is permitted
    if (nDataOut > 1) {
        reason = "multi-op-return";
        return false;
    }

    return true;
}

bool IsFinalTx(const CTransaction& tx, int nBlockHeight, int64_t nBlockTime)
{
    AssertLockHeld(cs_main);
    // Time based nLockTime implemented in 0.1.6
    if (tx.nLockTime == 0)
        return true;
    if (nBlockHeight == 0)
        nBlockHeight = chainActive.Height();
    if (nBlockTime == 0)
        nBlockTime = GetAdjustedTime();
    if ((int64_t)tx.nLockTime < ((int64_t)tx.nLockTime < LOCKTIME_THRESHOLD ? (int64_t)nBlockHeight : nBlockTime))
        return true;
    BOOST_FOREACH (const CTxIn& txin, tx.vin)
        if (!txin.IsFinal())
            return false;
    return true;
}

/**
 * Check transaction inputs to mitigate two
 * potential denial-of-service attacks:
 *
 * 1. scriptSigs with extra data stuffed into them,
 *    not consumed by scriptPubKey (or P2SH script)
 * 2. P2SH scripts with a crazy number of expensive
 *    CHECKSIG/CHECKMULTISIG operations
 */
bool AreInputsStandard(const CTransaction& tx, const CCoinsViewCache& mapInputs)
{
    if (tx.IsCoinBase())
        return true; // Coinbases don't use vin normally

    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prev = mapInputs.GetOutputFor(tx.vin[i]);

        vector<vector<unsigned char> > vSolutions;
        txnouttype whichType;
        // get the scriptPubKey corresponding to this input:
        const CScript& prevScript = prev.scriptPubKey;
        if (!Solver(prevScript, whichType, vSolutions))
            return false;
        int nArgsExpected = ScriptSigArgsExpected(whichType, vSolutions);
        if (nArgsExpected < 0)
            return false;

        // Transactions with extra stuff in their scriptSigs are
        // non-standard. Note that this EvalScript() call will
        // be quick, because if there are any operations
        // beside "push data" in the scriptSig
        // IsStandard() will have already returned false
        // and this method isn't called.
        vector<vector<unsigned char> > stack;
        if (!EvalScript(stack, tx.vin[i].scriptSig, false, BaseSignatureChecker()))
            return false;

        if (whichType == TX_SCRIPTHASH) {
            if (stack.empty())
                return false;
            CScript subscript(stack.back().begin(), stack.back().end());
            vector<vector<unsigned char> > vSolutions2;
            txnouttype whichType2;
            if (Solver(subscript, whichType2, vSolutions2)) {
                int tmpExpected = ScriptSigArgsExpected(whichType2, vSolutions2);
                if (tmpExpected < 0)
                    return false;
                nArgsExpected += tmpExpected;
            } else {
                // Any other Script with less than 15 sigops OK:
                unsigned int sigops = subscript.GetSigOpCount(true);
                // ... extra data left on the stack after execution is OK, too:
                return (sigops <= MAX_P2SH_SIGOPS);
            }
        }

        if (stack.size() != (unsigned int)nArgsExpected)
            return false;
    }

    return true;
}

unsigned int GetLegacySigOpCount(const CTransaction& tx)
{
    unsigned int nSigOps = 0;
    BOOST_FOREACH (const CTxIn& txin, tx.vin) {
        nSigOps += txin.scriptSig.GetSigOpCount(false);
    }
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        nSigOps += txout.scriptPubKey.GetSigOpCount(false);
    }
    return nSigOps;
}

unsigned int GetP2SHSigOpCount(const CTransaction& tx, const CCoinsViewCache& inputs)
{
    if (tx.IsCoinBase())
        return 0;

    unsigned int nSigOps = 0;
    for (unsigned int i = 0; i < tx.vin.size(); i++) {
        const CTxOut& prevout = inputs.GetOutputFor(tx.vin[i]);
        if (prevout.scriptPubKey.IsPayToScriptHash())
            nSigOps += prevout.scriptPubKey.GetSigOpCount(tx.vin[i].scriptSig);
    }
    return nSigOps;
}

int GetInputAge(CTxIn& vin)
{
    CCoinsView viewDummy;
    CCoinsViewCache view(&viewDummy);
    {
        LOCK(mempool.cs);
        CCoinsViewMemPool viewMempool(pcoinsTip, mempool);
        view.SetBackend(viewMempool); // temporarily switch cache backend to db+mempool view

        const CCoins* coins = view.AccessCoins(vin.prevout.hash);

        if (coins) {
            if (coins->nHeight < 0) return 0;
            return (chainActive.Tip()->nHeight + 1) - coins->nHeight;
        } else
            return -1;
    }
}

int GetInputAgeIX(uint256 nTXHash, CTxIn& vin)
{
    int sigs = 0;
    int nResult = GetInputAge(vin);
    if (nResult < 0) nResult = 0;

    if (nResult < 6) {
        std::map<uint256, CTransactionLock>::iterator i = mapTxLocks.find(nTXHash);
        if (i != mapTxLocks.end()) {
            sigs = (*i).second.CountSignatures();
        }
        if (sigs >= SWIFTTX_SIGNATURES_REQUIRED) {
            return nSwiftTXDepth + nResult;
        }
    }

    return -1;
}

int GetIXConfirmations(uint256 nTXHash)
{
    int sigs = 0;

    std::map<uint256, CTransactionLock>::iterator i = mapTxLocks.find(nTXHash);
    if (i != mapTxLocks.end()) {
        sigs = (*i).second.CountSignatures();
    }
    if (sigs >= SWIFTTX_SIGNATURES_REQUIRED) {
        return nSwiftTXDepth;
    }

    return 0;
}

// ppcoin: total coin age spent in transaction, in the unit of coin-days.
// Only those coins meeting minimum age requirement counts. As those
// transactions not in main chain are not currently indexed so we
// might not find out about their coin age. Older transactions are
// guaranteed to be in main chain by sync-checkpoint. This rule is
// introduced to help nodes establish a consistent view of the coin
// age (trust score) of competing branches.
bool GetCoinAge(const CTransaction& tx, const unsigned int nTxTime, uint64_t& nCoinAge)
{
    uint256 bnCentSecond = 0; // coin age in the unit of cent-seconds
    nCoinAge = 0;

    CBlockIndex* pindex = NULL;
    BOOST_FOREACH (const CTxIn& txin, tx.vin) {
        // First try finding the previous transaction in database
        CTransaction txPrev;
        uint256 hashBlockPrev;
        if (!GetTransaction(txin.prevout.hash, txPrev, hashBlockPrev, true)) {
            LogPrintf("GetCoinAge: failed to find vin transaction \n");
            continue; // previous transaction not in main chain
        }

        BlockMap::iterator it = mapBlockIndex.find(hashBlockPrev);
        if (it != mapBlockIndex.end())
            pindex = it->second;
        else {
            LogPrintf("GetCoinAge() failed to find block index \n");
            continue;
        }

        // Read block header
        CBlockHeader prevblock = pindex->GetBlockHeader();

        if (prevblock.nTime + nStakeMinAge > nTxTime)
            continue; // only count coins meeting min age requirement

        if (nTxTime < prevblock.nTime) {
            LogPrintf("GetCoinAge: Timestamp Violation: txtime less than txPrev.nTime");
            return false; // Transaction timestamp violation
        }

        int64_t nValueIn = txPrev.vout[txin.prevout.n].nValue;
        bnCentSecond += uint256(nValueIn) * (nTxTime - prevblock.nTime);
    }

    uint256 bnCoinDay = bnCentSecond / COIN / (24 * 60 * 60);
    LogPrintf("coin age bnCoinDay=%s\n", bnCoinDay.ToString().c_str());
    nCoinAge = bnCoinDay.GetCompact();
    return true;
}

bool MoneyRange(CAmount nValueOut)
{
    return nValueOut >= 0 && nValueOut <= Params().MaxMoneyOut();
}

bool CheckTransaction(const CTransaction& tx, CValidationState& state)
{
    // Basic checks that don't depend on any context
    if (tx.vin.empty())
        return state.DoS(10, error("CheckTransaction() : vin empty"),
            REJECT_INVALID, "bad-txns-vin-empty");
    if (tx.vout.empty())
        return state.DoS(10, error("CheckTransaction() : vout empty"),
            REJECT_INVALID, "bad-txns-vout-empty");
    // Size limits
    if (::GetSerializeSize(tx, SER_NETWORK, PROTOCOL_VERSION) > MAX_BLOCK_SIZE)
        return state.DoS(100, error("CheckTransaction() : size limits failed"),
            REJECT_INVALID, "bad-txns-oversize");

    // Check for negative or overflow output values
    CAmount nValueOut = 0;
    BOOST_FOREACH (const CTxOut& txout, tx.vout) {
        if (txout.IsEmpty() && !tx.IsCoinBase() && !tx.IsCoinStake())
            return state.DoS(100, error("CheckTransaction(): txout empty for user transaction"));

        if (txout.nValue < 0)
            return state.DoS(100, error("CheckTransaction() : txout.nValue negative"),
                REJECT_INVALID, "bad-txns-vout-negative");
        if (txout.nValue > Params().MaxMoneyOut())
            return state.DoS(100, error("CheckTransaction() : txout.nValue too high"),
                REJECT_INVALID, "bad-txns-vout-toolarge");
        nValueOut += txout.nValue;
        if (!MoneyRange(nValueOut))
            return state.DoS(100, error("CheckTransaction() : txout total out of range"),
                REJECT_INVALID, "bad-txns-txouttotal-toolarge");
    }

    // Check for duplicate inputs
    set<COutPoint> vInOutPoints;
    BOOST_FOREACH (const CTxIn& txin, tx.vin) {

		CTransaction txPrev;
		uint256 hash;

		// get previous transaction
		GetTransaction(txin.prevout.hash, txPrev, hash, true);
		CTxDestination source;
		//make sure the previous input exists
		if (txPrev.vout.size()>txin.prevout.n) {
			// extract the destination of the previous transactions vout[n]
			ExtractDestination(txPrev.vout[txin.prevout.n].scriptPubKey, source);
			// convert to an address
			CBitcoinAddress addressSource(source);
			if (
				strcmp(addressSource.ToString().c_str(), "AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa13raiuRHCu6faEzPHZn8NWN4GeE6ZXMp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa1AfQvCxtcr9mJ1M9n16Vz7Xngh6RfDts") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa1XYQwNzkRviJMjUmJ4VevzwC2ZL8UnPc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa2Dv3qrFsTHKxeQ7rvYzsfhQXG4yGMpZ1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa2PWEMXCbvG1sKLqoPUamhLAYFX43iPTf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa2XiYJydHKVpC9F1ugHZgVHTiRGvCi6jg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa351WnacotQJ3NQbWMLMeU2BG7uTtXQDz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa36jxwLXuZf3KFnZWJFoATapWWcXzZfmg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa3Gw2mQoiXk9x6niHhoEyyJsHWH5Jch18") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa41JdCMYiyP9s9RkarRmFgkUPsLA1CUjE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa4QFZ73TacTN92MRRVDX4dLAQSskcbFi3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa4tVXwFwyTfSp31vSCsAXaJmBgi5Kk9ZV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa58HasJv6R28R2xLcjZGAbeu11TZACjuc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa5AeHru63iTF3fZdrYmchPHWGpUcWE8fP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa5APd72vQ9mf7RB4F5HKLcWziKg2H6kuz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa5KghzefEVwMu3SWxhbBq2x6jhq9wBo3F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa5uYqxirY83Cv98uoJYvSzmyqEncK5LQ8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa638JhWBafR5MbHTF1DEa1pU3ujahb6So") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa6xkF3YUE7qDaHMFtpXJN5pftsYQzfUmH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa6xpx3V9842rudwMtGMtqqD46xsXiaSfF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa7pumfnyXpGNkg8Vvm1dQARTt8nJPwDyB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aa9iNPWhm3W6aypB4hKWCnNvZtbpAUbfF7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaaBUDrpQ3kZ3bH7c3WqLqHwnHG4MYsWWb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaAkdEyNmXPGeB8X7Fh4iBdzqP6zGHyAUJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaaNKLKbufkwwzpokZASdbDFoeBmvQATwi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaapxtXnt5hzWs7yiuw5UL9VUAa4MdnFDQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aab9aj7tB8PjuqjcTYBnpY48Jz8AtM9azt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaBcFPWQHEonUPoBCPZXwuvtqW8mv3ozoK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AabRieJ35JgYRyDiq8vC9todVd59HUZuDx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaBsRjmYKzedL9JVGwdQutbzFYvcWvsGmB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AacAmahat9t39mbwjoqLHj5h1WQc1deGZe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaCD9qaepBbYdAv6WcFSLrFNdo79F2A5BV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AacFeBR7GUWYf67uVuHFxc4iTrN394hH8P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaCMHUYBbyvEatjks7b6XDUWGsjWp3aD5w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaCtfgjbjMWZgbQ5XKZPoSysFS4QAYALi5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AacXKsXwzjr4LZaWyMnMSB7nSX62yypHwF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaCZKGTJxhcAmwA6qDrUUrcQ8Btix7ab1i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaCZWeYb6T3k6jzJj6Spuu4386UHYPr4z9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaDDmLc35YnyETzpv9GHGW2dQrwPDxxW2v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaFAXMRr9TB7VxpuoduES9okw5VBXwk8a5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaFcGb687XmQwn39ed7CUzU6RpK7XoXrEv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaffRswsDBQyP1sArEHsXc63s4NWLvVRzc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaFZ39meuCPfdvhWWHJ1rnCn1Nv17CqQ5L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaGDCyYpNJYEWS5ngRFbd5WLwWKxwecNYH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AagFLq2xBaGSn1YXcsQv5eePmSTcwqqXAB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaGo86AGDoa9HEVSEfA6HNtWLNrQyawy3w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaGRupum6xprCo53ScuATST5eVeqcmJhaR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaGsb7jF8YsHftbDHG1GNtWwgLSBPAbp8y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AahbadWoprn1BKRE2Yr3JgfMymPTEZnbac") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AahraPo538uibj6x3iFvFbc7LsykAAdTPW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaHu8HNF37cfBgzQBsiJHNZj87V6FbCprp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AahW5QHi38VoWUb8oLo3AaSDBGd9kc6cDi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AahXqandFro9MJzqngVXP5T6nCJKiGJrDM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaHZPSyQ9YLQFhy7osFKtdcu5DLCQj2JZX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaiD1y7GJBm2fQzsSV39K8pHPJrmswYhRP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaiRDeVQguRUe3gBm9cqb6fSFiX4htiqjJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaiUXdhnj8gcpK5xxAL323W28ejYpYwR88") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AajAfW6Ah9CQripnhjBrLJFWBqjx27m1Fd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AajFG6kRY7aXFGcAEKhfAeq4AL5ZB7gxAX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aajv6GdMmwm7mDJ95ES2mPTctxQaKtH9nb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaK3vAoxBoNHi3UmVyeoH1ULjK2B4KsS7b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaK6R8CVrzB4mJeGfXX22HPtNQequQtzDc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaKAZDwwtTNkTEFS7knwu3JfKkFQQXXXom") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AakbPYaCb8UP48yBUfsP1PrawYNTDqfok1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaKG9a1SJN47nSaNRckbPNdAUqyb2ADRah") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aakhp1248Anpnta8xhZykqroqPbmX7mxLB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaKHqMkCsxEnun4xhPuSVfp11AUvs4qxco") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AakLWtBDGa4NEPxdqcWVtuh3u69Xqdzkzv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AakMRYV6AzSyypZngTiztVEzujrqHJth9B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaKN93bwZMYe28kBd8HKNwg1G5JuWP7JMp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaKtw9q3gbRyeSsvDjk2jEUzhAKSEiY43q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaLkPZ1EEN1Fkzaro41DuAwb1cP2SQkMwb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaLsCLBCHS3KVMkxQDQBweYWcvRUajTRyd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aam63NRvrVNupVkSkkJtpjikykjmb665AH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AamcnPaGwZ6uJpJy3SHRbYAL8dhj2ta1mq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AamDwrAKSwDvrEF6CBwDFbFctMJzbvxEVM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaMMUcdi2fARwpDysL6m8vGhfdkM1CcVhk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaMUkT6UnAbdsyXLmYd9Cr2mdva3E1wLDt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AamWkGnG3nxsSvMefkMvbTyZny4ziKYSpj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaNacdTGgpybPdsmKZRmCDZoThVXyNdEyF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AanhJ8AbRk3P3n61v4hYTjSLDdjFBhBoXK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AanU2tns7yq7Mh3vyfJSK32jSqUFXUiQ2u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaP7rhyR9K4ATxm6LKD9Cpy1CrsjNb4z7i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aap8GNPSQyvDoEb6cf8ZeX9vE5FdomXT2w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPdJyKfDxnNsoXBuHoN5vF9338NkP966z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPG79N8SMng61Vy4SFNNt6z85uJz3KkaP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPhwQ1zgx8kSxNoHpGeN11qau1Uhiy8pq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPjTEUaRUHUmgHwBQWx5Kqx465pe9h1QE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AapnKkuR6vbf1AqxiLrcbTqc9QDKRkgFSg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPpsq223vnVBtqVp9wxRDSBHtUpqbLwWp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaPuzJbJ2T6XtBeEPsguJUgQYQeTRgKDiv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AapxSc8SPoCmuByzQNMkUCgr9qQ5GxbHsK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaqJDxWa7g5rMACVrd1MXhvY4hoeasW7YX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaQZbPbAWPm971BQmcPRkqkqEKHMz4DZGX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaR6p9EfuPTVMpMBGhE57VmvEN6S53stZg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AarbcnL9hHEu938uRe38qHipgaz1BB2zm3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AarCs1L4xn8BiMnaV7UBKtoRpikbjS5uWf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaRDzbY3TPNXGedriXwDPMvfNeRq2N7Ci4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaRga5guuGkK7v33deczwmoUUWzq1pe8Jr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AarswKf45AzU4kWiJNPRyfFKkDsuKMDnGL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AasDPdxWXJE3yv1UVAE9httAL1xVg3Avzp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaSdXwCGdSZ7k4Rge6j3KrTQ1LjUuv7YQJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AasFFWsLnEkzxfzQApVvKndZhRXDZAp9AN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aasj3M2X9pMiDm8WNDDKsKEweyyVMCA7rd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aat1gU2mSo6sH89f67obk8Vezf1GNB5py6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AatbKYuKXL111121bryUTGPpJcZp62xUjZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaTFtWMv69cdqriX8nDa8Yq2Vxtgvo3Ah9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaTHyJ1Ps19PG9r4fPyrmZet8tdsoUZHxy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaTLfmRsWF56t5Z5ix4ZkuhjyXcFSK6UTW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AatPPLbQDQLMrr3cixXWjJcz3KZV2s6Vhb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaTQT4Web8Tq9LvQgCXX7oWcbN3vrTV3Hk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aau2AA3XraGGD76e2LdyRQRtsEZJ3onP4H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aau5NC84iGjiX5XcJPNsKNRDvMvNFxREbt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaU7H4TyfWFxCe7mkWZqeduZo2eQ3s1d24") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUc6qcXRZmUjqto5CkbksdutDngb3RJeo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AauGqFcjuA1QqvcW6anDvVqdrcHSsXeLw7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUpEhZQqZ4Sa1yh6Cu7D1Zm4QXt4hdF8r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AauPJwUvs1ChAHdWJCmoKVH9iCKQjB3pWW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUPvevmqrg2zzfphxMBr3UDtsJ2NaS262") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AauReVLRC9eb63zWygK6CqgqWfLVBg5ARG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUUqTSK4snx8dmJrNjd9YHtNEJKy2gJqj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AauUZrYyqMEwhnVx4ecUozF5cr9z6oZbiX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaUwPXBjEFVwvaEUGyCgKKgUme6xJQ5gpK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aav1Pv2zfVs94KeWZ14ZbbKmfxASmo1Uaj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaV5pMiwGSvvNQ7FYTr7Tw2KzDocZHUwST") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaVaSUCVUh2cNvqQRg5FsypJwqDBLKE3Jz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaVWtiKiPy283SiGwMvMVfqVMTSdE7oknm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaWaQ6cRdGjawR72crntzfd4HjoCSWwPJj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaWz7c4uzgUwoCynrDiodKcfGksSEi6FhA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaXE9gYrA1qWSXdJgKsrWXq9CKXLvkX3MY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaXHZHYLJscRZ8hEDXAtKaJXEZftCyAX5v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaxLcypUKdBi4hnHwsusdK1Q6jqZog7atG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaXq7pcUT1g9FeurXMmWBtDhZCJfK1JZBj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaxrjuoDVQkXLSY6sgUDcTYc7Zj6CGX7Wg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaydkgRKFEWoSAruqpmvQnQFv4TbQb8BTa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AayoPibQuwYeqKh1CFLzYvUgG7mUwE6WUt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaypxLFgabfGx7NwDKhiahJVzcsR7bTSbx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaYv59LyG9mrwNEruCfbRtwcy5mJun2ecr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AazAVXaUUstSDT3RoQx2mSbmBo99ne7N57") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaZfMzGpdfMH9SqB22uNrdzpjCJ3Xrsb9t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaziqAwGz6zD2Pti5c2J36rvrLLvtasiW5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaZNUdJBNNCQ1zgGNWPn7F5fJp6NnZH9nH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AazrCPeWBvwzwCpqNiyWKSUKVRVFJ4vPze") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AaZriQAgh7bP26L6eqCHTZfeAe6ZVXRWaY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab1DLKpJ1fVeccjG1ELkkMDv9M7nyNVXQM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab1v5kcyKCrE8Z4rrFoS8Q6nBiFgGYPPEw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab23FSwvJhzAh5GxAoxdRpc63T3CBxs74e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab2D7uxErWVVEJwpiALmw2ztVtEMKsqDxE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab2Q8tudQGHEtwRHUTicqorKiZkZopH4x3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab3Bc4RtsPuzeQgZuZ4DuVASAiqCQTbjsD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab3p12LtourhL3bimLe9c1DiX7XwUzc9ks") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab3VYo6D3MkqvDhmQ1hmQLUnssy9VdacNF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab4Hetn5jKtDRPZn4ppajxbVN6FcdKNUKS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab4RnKJHFyztv7AywZPYu6CxUMQbYVff9H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab5MFiXo4EEignhTUAQ8Ddj1AirUA7wN2j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab5Vbn7v4YPnmNWDx7ZB18fdPDcnQ1tFUD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab63zwzvEy7TnmzMtyZeHK1WYdrjsW6fQY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab6ADPZ2qyRS25eeH9iAd5RvauGcMba9c9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab78tCWmrS3iRFvSojYzorDw6RpaTw5bkZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab7NsHL2Ci7brqzdfz7KJv3KYMGMhXXQGa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab7RVE3RbNSSzgexQjScQ3C64R6RmfM1kt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab7W8SGzYFdXNCHGJ7PjPafia5ZMSjrL5H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab81Q7LkiDLaT2aZYMeLFWWGvWX4oKSEcs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab8i56GBvzattDa6F6RnAA277ZArjLqsjn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab95XxmTK8Ex7yMnxK2sqMHzveDFn15VAe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab97u2Fs9B6bEUqR5Ftnt3rZGbJUsBqWji") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab9q4AyfYYWXcZP99DSYqcP3ZLroGAhDVd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ab9Z2h7fiLtNhkhrGeqW617W7PTcZ9Xdhg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbA63QgYLmXr4kXgz2JxHYzdrzvCkQttDK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbaAGK3iPZUzpVoo1QD7HzUuDmqcYixLAS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abad5rVcYL6zcGU1Z4dbjQJ7tEBbfCzm1N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbamSU8GpAfnsDXQ5VpDhW51gCEqRixNf2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbauPERL5b5e9iKmkuAigZTXJCYVg2SB5K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbAX1Dv6EHrMGcWJA3NcaiEzp4JnzhtqGU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBAi8VPsH8dg9R37MWEMJZduq8oExW9TH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbbiyvfydRNbearEfaYmTn5W2hdbvjh8jb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbbJ4DqbGqnhkKubaNecZYv7PCicxKexoz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBkGCJc2VmgBZwATS989nXBMzyodntiZa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBMK2pddacN85MEAjpthSnRbBn37N8iHp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBNqLHoNJr5LKAsPE6uAP8YEFB2ofQhXY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBTxjeg2UbQzzivAQeWsLxVyhkJ53GcMx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBY6aVAt5ww3XRzAsKfycc4MJEfrVcEvs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbBzWjkSa4sZykkV4KTZj2Y3gtdApQ1sHX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbCBMSesiWbaiPwMgNMifbG6WBT33f2JwX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbcLtTEpusmdc9qMhy27i1BtQwhYcT3psy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbcN6u2aJNCKTn2tmw85NVTYUnCKgajCAu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbcyZy5ikHdi1e39FYDqNNHibBbfkftCbp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbD4awSr4wygu57hG8kSQWXc3yQpYnxPnJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbDdT74DZxYmp2dwKgjwtcmvr6FN6p865H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbdmM5cEDQYsHVUMzdfcZbBuTYzpjAG6x8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbdnMT37QLKjVBdot2sHhyKHJDMHcx9c4s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbDV3qQ8vBdkeAzJgkiFa3xrKbKtGFdFXg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbDYG5CiD2dKoy3Ttr5MdUvqVDJq2xSmNp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbegJt6ZReFshsz42qhE75M2W88Vv9TPcq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbEsvwLiAZaRm7KgYWj3bVqxcNWHx9swTb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abet9pGbrCZ1YMrQqx2MeKhP1whr3qz51C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbeTokvjL6aGMK1UMNPfFUmBaK3Lduk8DR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbevsG9VuWyyim3fJDruLwxRePqTHL9mzP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abf3ofHRZfTdKPwx6mMiz3jrWjKcS6cux6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abf7SofeHBAozpYpLxjPwF9Tr2kriTxhqe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbF8zu1gtdmoH89JbzcS7EFG6wosemKVPj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbfhrwzBrPWwXf3gkSYHKJZ2Ehb9Krkn6J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbFN65ZrHjcoPhSFPB2p8QM6psL1ztrovp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbfUwrQ15XqxgaiA5m4KfMQfT9Gs1tq8Kb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbFygfpTaHVWhvb8M8G1ns45GxAWQSoSLN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abg8aEi2bjj9jnR1JY5Fzg7eDn9eznFBoE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abg9fczkbVaxbZHiNWWdSQ9DEeLoeuN8ig") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbGA7HKnuNKyzsMGQWM29tbswZJ3zH8kkA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbGbGTXA5UQjuzJ4MbqnHDKfY3RRCSVjPr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbgfwNtbgdbhnFk7tecw9SM6eCmKd8DHkN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbgWXniuzU8hatvBBN13EUgv1NJvARa8Qt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbgYZEk7zybgfioYJWR17GqTYB2Sg8u3ua") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbGzwnxb2HAfWj3HLvwFisbDnBEhGAVevi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbH265iuVYBz2r9gv2kupEm8GYU23YPkPG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abhdn1Hdfe6QhHxn3BbdiQY1q63RmtuZzE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbHmBnUymoBghrZq3ff7XfUhJSBKFwCxqc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbhNpTUjkewAPUHaLuf5EGjZMHe7VueTXT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbhoapSp6CmXsKdXBWDrCWwgTTMB9kqDXd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbHobuYzEDzBvtj7wAuzk3qLRN1icaNpaa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbhpWJAVaYH3HekbuqyGDbPoTwoLZabRLA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbHQ45iFxqCq2TkdTpBugnvKGv3Ha2qUTy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbHVWP2anYmvDyVoa23fxbVEooKFVmfTJN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbhxwBses1KD2ovRgAwN1TqY2MLkdeh4sj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbiayAQVRbgJwQMv8oQStNiYchpzyRer64") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbicwBJj7tCAVkxr13utFp8nheZhk4TA7R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abipj7Uzitm5HzHDAm3cmkwa2TqHrhXEwV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbiTy4ntAgDo8JfeyvfZvMbfDBYcSixkB4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbjeXUCgjrjUdysA3bxt2N2pGNXU79Djih") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbJiiEybMWwsVjPT9JikZPoBFRXzfi5bi8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbjKEH6rzK9VWokfPU2BvgYfsZCPBN7oWU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbJNieti3U38xqWrMQa6vYuzo14VWyeWVG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbJRCFq5LDpFfcVr6vqFFJ9TBYPgRQXH2X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbJrCMmoi43kBLmZEtwfReCnHDr8VXzKG3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbjYFSnbkd1mTzJAaorJ7q5NhGVHQfo8ix") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbkdQniqSSxY52vtBurigXDwARNs7HaTv7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbKdzBW2hiWqvumdNhoYhg1c6QKQrToCVE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbKiAcseoWTzkzYy3mSpMT34ht6Kgtfbyu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbKT6W5XshrzpNFWJqyvyy8g1gBEa1hFkM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbL4jfjqiByWpdZZpHscQwVchZCM7cusqo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbLbbtaK7HcYvn8T4Z6zfWL7fv6hYTGFZN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbmUVM4QTbUBuZBAGhk4krPD83z4fbQRCD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbMxLripcusNG6knRXBJ928H5vVwCFBPez") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbN2aR16SUicao7HtBmNnHuxsib66i1MJn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abn9G323kVdGqZRmWaxzpTxutsBDN6Tfh7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbnaLrQCR1z8mCYJKidCnts25uASmpb65t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbnRabpJLU11eZvx1C4GdwtP1khKFqxbRr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbntmJk4zsxcEQZdMyTqxSGX8AgJhKdtdH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbnuBbyu89E8ETXNVNYVhDgUrbnG7nM2u2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AboAhAH3JpojsTrAoERmcpN8Njpzt9yJvj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbocgmcDWz5P915EV4YtzQa94qEFpohLzA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AboZUSWhEqPdMYuL3ogDKwpboHA1ENvzCP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AboZvouTCoK7WFti1i6UaDQXfuxSfEa1Yi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abp7Mv6pszkb1Ruco7dsJ7p75US544Rspz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbPe4RzuJ51LVTza43YevooDYb8DKadC4j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbQ6dfmwV7KzM38e6Pz2QjNkiFs3dztMh6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbqbBusL5c6Nbh6zKGu9TnSpWcGFqaBNhK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbQe1CHTBpSXNjpTcYQTchbAwvK3phef1B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbqKBPWSqsBqujVD2W5sASXXB3iqtexcor") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbqVthufCN2X2Ni1XMmRs381U4nsZBFT4i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbqwzC67KS7Gt47KZw2sbd6mFwJNwExps4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abr11HEmESjSBKiccb74oMqdMJne8Bza57") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbR5AhBWkVcf9yqefwWjh8bZxv9Q1vNKQ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abr5bhSzepd49X3i4rj7XhyXxF31qcPsmE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbR7HcofLXBiWSwBz6csUcKBxBTN7J6PWg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbRG8fhuMvcrPe4W5xYqBQhpdE1PEbZcgo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbRTnbUFZjF2v2Z1tZggtLE4Er3Jptp1jo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abrup3yfyUw3pas6i2z81qgUkzWP9RAnnb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbrwyGnnJEnwGdbHxC52RXAhMjASgyYZHf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abs8aSRVRmBsNH4QhRDixuVFTDrTrU98ae") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abs9GhAQD27xJN5Gq4quV5EDoJS5r3zZYT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Absk5MEgfV3qR8B1eZdE6PuCRmyqujHFPc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbSpXmTHY1VtnkaaPXVvMEUkzcMaHutG6d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbSrNBmi5PVLuWewoPnniYpKiCxDEn2zLX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbSt7bRHdvNYtHrUJpzvekuZxyw1WQS8XF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbTBEAWJopzY1sbcQskbi4LqJYS1q8hfHd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbTmjHutuM614EpYFqR4dfjyr5dDtwpDh8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbTqdon8dgDCXmSto9CGoPeSRW88FARSnt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abu5J5GfzodvBVzyPQGES3BY9vJBGRYaE9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbUaNgavANevkpy8zb5W7bZX3S76pcqvmB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abun97cTJfEZx6MQViHqZywWhUabRPdfK6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abus5j9WL6x7y2Z3eCsHkGW7JUS7ShN8RT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbuU7MtfKTJMtBxjcZ5sR96rmJBLUDWVWC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abv5hxXLK7GiNnTCjdFkfyMjiEmEDZLHgZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abv8x9GTKhnwmrphwt8TVQHeEwzGSnJRCb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbvgKbF4swqnLWCTPcmhJ66kcgEpo1u417") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbVS8kQVB9NSVXhuGCtYM63uVPgFitPfru") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbvZm7sMPXYQpcTjvJbom6YTSBQgigGh1G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbwA7TifgNbvu5f4tbh7cVMx3W8uHxiJE1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbwDe13FER23AaHEPCMuvScmzHV362xVnv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbWDSFdrwTwaKoUodp2Qoaud9rtPeL6dva") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbWfn62PWLEmayrCANeLbe9GxNS4Wd6EUy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbWJFPFbcqv6F497X7VFq82pmmuZQ2dkzw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbwP2NBqtwgLMR1yNvuNJSNMQYwiapGFWX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbwQwJVnNovWMMznhSbqVMZxyUznGARdDT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbwUDdo1obrrEJado2wMi8GrB6eDRfDNyY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbxbC6nXVEKJn9MY3Fx9mdawbB5UrSKjoA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abxc5Tz4mF2jAWT3DvC6wNTXFzLVSrhttw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbYBhQGpqVMaj1WJfMwmAQ53gpMzinS4Li") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbYN6RoAAvAdaHohoydKo77CqFqwUunvee") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbyQFtkPWBfT4DyXum3pQBJrZHTHCcqqWM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbYQhxGC3Roa9LxkHzjwQvhvVKqTDFmcQX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbZ3YmcywyzuvpdH6N4cEgdVvGbkPkqeR1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abz8QUrPUZNY9pK6yWqaopboic7Dmf5RtG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Abz8WhYjUHJXjqkbegy6dMYtQP251Z8uAk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbZA4BB9mmdBvbUi34oN5j3UdvUyrXMVbS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbzktadeDJpNxmSDj4WKqoXvtFH1C8ANsX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AbZu7evmwnMptbz7e82h1jBEDua4Sjitu5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac17QdwRwRbdp8d5u6JazcQ6pz84XPYEvM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac1G4X5v8MLEyRDxPGespTYz3We4doGWdm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac1pC5fRZkpBosVkLxCMMtVAnjYXPQ5Vet") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac1xy1ofpPX65eTVJ3APf47s7pdagbFjrW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac2rRqTNDZeVUHKzybzb6jfC2oVUtuJqPP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac2YtFQzofKtqATY5FPfKHGssrSJxfvSUZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac3U7yyYaaZsGBCQExm9QstcG5mYVRC16G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac3vJgGuZSTPzBcyCgfNFNFNp2UVRcqEe5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac3ZXAmdmN647bS6298RQ8h3GAyYqsShGA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac4ae43Hef3Swr2YhY3mmBwaUg95QjpnXR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac4hrn5TsHQW6H7Rnwm3y6rCWWgCRN1Lbe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac4SxcEGQSDsbghzkLLPPn8qwB9d8eiZ3n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac5Lu6f9xcDcc39fRmkr2xHLQXjruGXyEx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac5MqggyqWyJYR3LPQvD279dqqMqVfC37G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac5rhtgp8FKXy2LKJPtXKcB8SdmY4qsPEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac5tdr7sornA6RGC5iPSGRBqUKir8e68Hd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac5VV6hfv6wo54iFw91CQpysCvqTFiKs1V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac6bqJuJVfW9f2rd79VqNw339htwDNBeMV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac6c7JH1YF3vncZYjeYkJJJkyzJxDSxQAY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac7fV98sR9o1avcAL7uBvEWBLLuTe7gwSH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac7NADDUtsYFY45FwVL4HbVA2WiWbNGmd3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac7wpNYhgTbgdbpk8eQ4aWwF5xo2jktm7M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac8LvARW4htkob3nNVt54V1x7c9QXdxLw1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac8McFykWQbgmYqnnVFo7ivaR6x32yxiGi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac8qoAf3gSbRCcrWiqGcQxSohw2VRkW71e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac8wGcCMmGq7q6xjR1HUGuadqhxmMNns1H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac97SWBN5HkgbcQve3crXJLq5AYCEyk2k4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac9avsKsijDZyqJfYj7odCBD87VSsminx9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac9CT9nmjnoRMGMaCJ5423CZjf1hCTTPNJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ac9tKj2X9jCVMyLehjdZTnycfnSZ1M5jSP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcA1PyKi2LhYZwSFM7kAiJ59Jq2bBuV5Yz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aca3jzvvGkjFd5qyqnXrcU8cVvrS2CYw5h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acac2XkcborxsntkxcFCmyQiek8uHECCSf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcADv7iQTYWpDGkF1ocRYEDTxgJwqczuGb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcayWPfumbEdp4v5MAVLCUbW74YnJYhdVs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcBi1VfnKHnkGvC1mHR8DBeEh5EenMupkA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcBJN2UUYTubrQcUTYtWc1RgVDwM2mZzCS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcC3KmKGWtbvVktskiFWHffi18zJPjkS4H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AccDW31Y7THpPwhRGzbvdkHodmWrdDdQba") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcCeNhuvBMfswZY6HHBbuGgFScqKjmHLKJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcCPgicAegQTWdDusAELfRrLF6sfpjNqNc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcCSDXvPpB8fkEw4qfFLQUUDcHf2u5yKcr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcdE6whPgwrd1nXhfmLmcm7JMr95UFDJDr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acdix7yHbAdEmiZwVfxh8BPhg6rsqsHEm4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcdRRBvMjiTCtB5B9xfWJYq6J4fyvCZ5Me") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcDW5H38xPhwkibD5piTkXQTo3Ux1mwHTG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcDyyN1QvrgLaE1wrJ3yJ2sabmPKhaYRTc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcE22opdnhSvm5Scb7mztdbnfezAYz3ZJV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcebqsBAmMxuKpEAdrQx8mzSzhXTqxoDBB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acec1Lc3GqiQFXUP9qDcC58tAtgUDpt3RA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcEhhbvyKbSHnkZKTFdj1MYHEx6z3KeEch") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcEi3cKjbmZriUQQPeCdvX841pjQyPLQdu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcepeigUR8yD5GV2Z6pamB7ggRUcqQquwJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcEQ1LZ9x6tWUoAY3fmDKHZuVpcEzYamAu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aceu9DMu7JTGFsVzFtg47oMehRr7FWFHBQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcEyGJ6KYrjf78YCganF1DA3oAsD5CC9ZK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acf4Z9CteMsg2QQN24ZiTXkaBMZfvcfEwc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcF9L1KWbA5N7skcPGSUKLPNhbxozEb3iQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcFWzz56exC9yhN57igAfCFT2egv18eRi9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcgADH9oY2PoKxYV9yTJK1eBXkpCpS3p9a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcgFC9o7RJHVCJeSV2T2L2H5pc6W5dVcuh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcgfPiEsBRq8MkpPj8wXTcqLzetZdncAVz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acggj2U8SK5WV1eevod1RMo62e78ywoRgL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcGToZcRwF76zQKvcQwaGjUnErS9rVpkXG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcGza7urwKneCVcutJfpoZV6rq4x3J9nFv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcH4oh62zAJjQPie5eJ8XBHPnoRTf86J5n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcH4TCYakno7tHsMqG6tNh4Y2FGsFy8wf9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Achrkh64ycXs9KE8ihJV7QxsEt8gkfQcbY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AchRXJeSzyWKwZ39iSXnPHPttTH5Fxte7E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcHXUmWgSQnWotstMz8xQUDuwNHEYD3vdL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AciAaFJVfe5FACk6p45sMjoT7xkPYYjnYS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AciJtnAP1Hox3zsG2ZDX5g5WMTszU7nkzF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AciuEBAQv1Mp3aTkGbuV4XBpoGBX4neuZz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcJDNrApgzm9NBSVpWb83A2Wx9XnEvAMvP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcJh8jGiJefb8KjLpU7VsbLqagQ8GzuZMz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcjJPRry3TCjYUJrAiTmfBqA4jb83dZfQs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcJJYxWVLL6rDWxNV5UVgjJguLT91DtgNV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcjUdiJbyjFZCZNYUMAjGxr8tUiiraKhoF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ack1Be9KDiQF5dGVhkVaEYcMkHjM3MqFJX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AckRuvGYeCHivVuCYnwKB6GD6qig1myUVb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcLAgvppgZNKm8kzWExqyicpvZsfAQyoyo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcLu93zmzzWoJ5DTKSewkQeNR5QQ1A6HbK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcMdA8UDBpqniFNeBz64MyXv6LDw46aqJG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acn9XxQfotXBHgUZ4njcYiQoMKHZQf99xS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcNfiNLAL49UiKd1z1KWPDkbCdqTTeUuxp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcNkshHFusyaY8gu6ANF3cqC6fHXUXS49w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcNqKQFvtV4ptM2aTBKSWz6vQYTzdxikjh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcnyuhTPBRpCuAEActYvfZXkCZhCHGp82a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcnZ5acDs9tRvgAeeWSiH7yDkU2w6y2NjA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcorwABYa1F5RoMU5arkgccRv8gUNrC1LR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcoSbhbyixposQYcj8b7heisvwmaFehCR4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcoytzW2tFemw7k8Lpnq5MG2j4f5YWKkMQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcPghQtVK2PTwJmp5XP4ce8yTgHbbeFBBw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcpjjzKNHmMt5ZaN9QZPm7eoFqpexuW5ca") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcpqrTxhfRvhAooEovoCeEev4tmpU3tkHC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcPWnJGwcU6Mp92ETVjfBxh52vV1Cpkg4f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcpYFs5k4Qh5viE7Q8XUqa7i4qNWDUkBEd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcpzKsFHRrqCxVBgkdgs9LTogCnPCxHWUt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcQ8tbTCgjatDsjzwAHQHN243HRnSi8vG9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcqE8cm2Fb3wmv6tYWrKkFWXCCoKMYGjP6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcqkQ4kgjXXKsbuyt51BiggK1BJ143KroH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acr9914QWpCNuCDqdysMfeLTYfjRD4QFp3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcraT6rQQUrCGX73VayBvrcJ9jQPpRvC5g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcrjotwcC3m9oowtcjssRXajDtoK5fc7qH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcRqgSmoyARt4XBHvXuey6NPU3iviy5aVd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcsCkV7aQPm5azn6YSqYsY3wQY4znDEonF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcSGdz2LZricyWNQ1hyZKFWns6ppA9BYis") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcSKSF8AL31NtNnGr7xBAJsZLfJbtp2kJz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcsmsmabcGkGpKqJUkEnjQRJQ4G9HUkk4v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acspf9ZZG1ZtmZzhR8EhQnwFvKFA7fWNi4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcsRGBvJTHdD75DKcoNeN5yRGiMixpF8hr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcSt9euCUoU8WifLwcpUFGdt7RZtuV1YHS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcsthjU2t8ZN5RBEbzJkmT4Xy7FPpD58Ne") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcStyAT6EK79rK7ceH83eJ5bFtjD2bWSgV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcT3iifmSDgKBKpAHxMciBULFTxmhek2qQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Act5pUdqZcURMunSYM59xYxGPAEdENQH4o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Act8oZCAqxwRhtA9TQ6AsrDfn8u27Y2VBB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcTFkNKEPox8eKmwesPjNG4JjxGDKpFQNc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ActmMngFtbVqmTrKeHZK6r4sknxAaDjLpC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcTn5K4s7ePYD5FQTNaUYmVxkhRWZarwN3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Actv2XxZRMk64sXhoFAVvbQo2QimHL3kwU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ActX32pFtHKrGHW2H6dZoSjV4M7Nj4gwXn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcuAvYLyAxkt9gpjsSS3Uce59WWjchhoAX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcUCgpaxmbubeQJDQ1g2MCn3v4zKeMH3Gh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcUCpo91tYWqMzu2rNgkvQWehz8Jk5vKUA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcudZggEDTXQs8UncrZSjWwukCtBnTieNw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcuGhsL2e3USkvpn3XF59BRpdXrj8LxK4J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcuorcDaavNYa5dvBJP1KEm4ionhaGyXAc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcUTJJxctFDZinh1BR7u6a8PS3hWDFVwYP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcUVvZytG6GSPH7QT2VUx3kjvPEknz696e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcUwB9CFAMe7kbmftyHHkqPn4gUjkieb45") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Acv2E7npW7UCHuUhPQKbCpCG1CDjxQbrJE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcvgXgyafiWrsY2Fr6SmMHbqBH4ayri82p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcVK3neg9H3owJJTjEToKfR91fteBMrie9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcvszuMx61ZUafYbonYuPtZ5vswUyXP4jm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcVz1xhb3kZkxww4FhAPqxH4Gqhy9vcX6m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcVZheMePV6hawXh4PuhMGZ2znXGeDcoqr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcW6R1KgSdUJ4yE5AdVrEEsx66ecdFEAgK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcwgtaVEmaNwyXdrN8SA7H8AD4Mzake1Rt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcWMYaPGztY6dvZAgkjm685W7xXx7Yq2zW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcWqk9rxq2nJYXGqLNoFYmCVM152serYjB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcWrSEnpNYsDnSUayLj6yB3gCcpPtaZfdu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcxoBB2ACXU4HEv4WYS96iwSk9Zgf4WUsi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcxTT6UYhSBQq8M9ZHt5yVvg4gS5pNnyJz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcY9123Cb2HwvPCbmTADVZPfiNRXEaBUL4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcyC79H5uNLAmvMXG9eaw6e8HzoSebjMdB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcyHs3uLqRfzvMiW2TGyEXE3rvv2rnM6Pp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcYKaWrz9UwgFmkiotBLaU2qmKKpnEHCjG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcyL2wTFCrR1wBsJrqLdCGhZvZUehVDQkf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcYNaY9pYYLhjmTwkTAVqTKqAoVSrbyZs2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcynEoNDsVEdNQXtXurFoQGDhUMq3Fq9YV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcyQbUi7DkCbqyAJujZcgv52CnxUK7epPi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcYs7E2bAtZnJ71PUQZKzNhDjy1zLoxsPw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcyygY8L92Y5UeEGE3yRsnwt8yjzdXT3eE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AczA4XttVdkK6j6YMTgDrV6f51xqM9NG3A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AczD2roQGCz8x38tyET9He3AzY9LBrYb67") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AczH5gfQAoNnH1NcuXAZL1pxAqu2UvU1cC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZhjcaFtujhgvqvbPNh532UNSwvSRHuqd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZLyJk2UPA5zpakEMBTfP8PwDutwjaArt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZnio1WVH3fyMVyN9exvMzPBg6i6RNUcF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZU2NVXd2RwHk5ohoQbvBsHxFzyTZxpEM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AcZyirLxApUz4q5Nbj6JNGnsrS4H8Ne1je") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad1AsMQkfVS4aWp3HH5aq9qFRNEnWrXW55") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad1cMRhvY5K4QAX9as6kEDvGCMSZzBu2Kd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad1eezzft6VCDmUNx3sgTQznQuWYcKRToz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad1rehWdXiHHXwPuZPMha9gANefeWxMDQQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad1XyAWKvo1Fp2o3C4xVE11NizXiKpC7tw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad2KyAzweC75395H1Zk1QnvpNxbKGzbC7j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad3NkSnwkXnwkmCy4HpDXPsgrJQVx57FAY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad4Gb9uPiHnaCV8QWUcdsy4QBHyhbdTsKy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad4pYrJQds3fMfTrgoVZW3CkStXCB1pAqZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad4t29jkx2cDTQPPJQKw9pKkDAPC1Gyrg7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad4wcrwUYFKJgFPPS4hXQsfNSNVzrB3KDZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad4wxYt9PXDEekoBUH24gjanTm2M6rABeH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad5hXMWLm8NDu19WfjR89bumzD786njqZC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad6AMR7gBfg5jvigwPncD7SZsK8nj1rDio") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad6ko9m6Rp8Dc4HfNqPAtjYoiTmXfC3Ne4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad72AsEpvNKSRav2iuRw6MgD11kCD5W5aA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad74ooao2ge4QV5GxJw2aiS1pe7ZmqdNrE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad78sc9p2Hfq5yKrGwpgdzbzhLQm1LDdKE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad7h4pyzao3Twpjh5xjQvZ4Jpd8PiUEAJm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad7SiA364k9Gi9DuSL1NGqk3ik2cdvEhSa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad7XaPbUv5KKx1hXtjx7DbkvYBAfyDChUC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad8m4JbKgH6SSjV9EB2krTrJ9AGzzTNaET") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad9jkT6vrpGXysQKjcMBqn1ywa914qKXR2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ad9mg14rA6SRVt9SnJBDmXTc2cEqwL9Q1d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdADUZYa4DbCdCSkv8mXVQtSzG2Wf8ETMs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdaEHg1pjmBN9TDvP4J6CUA8DuxLnFXgxR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdaQLFcc9Wpf1HuMbw8hh4kE5zLhVdJdEi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adaz5fozY1HYnESohYd6pz6nzP5aGhVDyu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adb3RcWaym98nbDQ6ttx5Zy9AvKVjcLtBP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdbCkQ7TCNwG5t2cVSMFUSzKHBWhTC659y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBEo6V2dCfNR3QZVVLFgTPWmf2fXGZaZP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBFnaDCYzyudutguWyznzKCxFmxi21HGP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBH9gYE5v4KEzNpzYcRfyPSxsQSLoUuAp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBMpExUt73zqBy85NzofiFpKC6SpBZbom") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBPABaPfeAyteCktTD3B9x1KfYKMeXVHp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBPY1GTzneve7cU2sZN79cfYCNqzWGzbC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBuhqWvWpE1gYtExca2JaefS6uTjkXyEb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdBx3mfoDdU84vLiBe8Lv2nPqdXEXL6vN7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adc81sWnvfQud9xcRkjT4Ut7hTiuDiNZqJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdcBzdDx4ZDnTojhwHuRtUvorYNzQQXeeC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdcdnXAyTvfYUdGBJgYo5emfmmQvQLYHbX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdCGqX9DQWRQgLCYmLy37MA2zqbjRALQ1g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdCSen1vo1PqYHqguKgvHkm3rj338Tzuf1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdDaeDKoZHbx4DB17MKaJYMAm9rjE8tEpL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdDCkZupnyrpyWPzVFnrUu8tJt2DJ6aRvJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AddEGATtzP4udfM4UFEqfwDjoQSTGF1pfu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AddewpPSM5b48dnWxtp39kBVcVRn7C6j59") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdDj66QaoufV4pfZ7JfeTn4iCicUkEPcjp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AddU9ohX93PsEvFVbbyK3GcGRsSi9Vse6y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AddUFnoMoFjep3M6i2N9DDYp8sqHxSsCHn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdejZE713HDKovqr6G5uT31U6zja7KSyHS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdeQAYtL7oejYUjtpxMbDcx8HQngSCknPo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdEQZaqM1vq25XgeKm5miRjorxzMe3XDqf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdER1PEo4obmy2kLxdKFcXn5oBHjNAgnYj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdeXsvdQfopHJJ2HkzhqH3p22x3ctKa7FK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adey45xPQJ8F5LaRkiPNTpYpbTMXMViv5Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdeZzCUF3nGzkQyENi53SZEQk9QFUDiHkK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adf91P6S9GJmoS3GMJw3ZSU6s5z4unv8yp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdFm1FXyUD3UVQR9DXvJiVnq82xvR7WLkk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdFqnb3dxPvL6Q6zCYwoWF9hpVMxTEoMX5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdfscJt3yMwscZDw2FeGSELJDnHwZjKp4n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdFwRTy3AfraRhLwBe4Px1xMdnnGm7TRoW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdgPXD6zx7K1kNQfHskWP5Sf6rJTWZvzCf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdgVk5beSkQ6tmrRDBkFS5yNXea9xosaQB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdHgv8ob7kBTYVNHgRY27YTgnL8vseEPVg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdhsBtKnG9yNgSYC4T1GXvvToJoijC5wyB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adj6jDY297L3es2pemCS89ZGxPihVeqd58") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdJFcffqmizkYDjGTey2m7akRc14SoxnkQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdjKLckCdS63ncGnKfuxvQwUXUvysmJjyh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdjMJkCi4gNgGiVpi6BSyFGdyCPJF89tAC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdJmS4sPwsNax79WVYoJVUWfRiwviR5xjs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdjRcVxG1SjxgNZ9uSTSpyM4BWATWiwLLP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdjyQLL3fE7LRtB1QV4sUvSynJtvwm7SKj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdJzJGi3jbNvaY47kNYpbWpCmYWVKi3dXA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdK1QdquujJbvrR5UjmDFBvQhdBxZUBttp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adk4F7eBcQ6rLsJjbE2qux2sCgDSrJ3Ekd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdKd8b5z68mN8amV1D9xhpnAvkDgGSoUfU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdkfzLzBjfA6grnDsjtx8mCZD7wsR398ce") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adkmn77iwFr9djsrFQr8bCc9AZV4kj8HPN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdKNu9xEbszYqi347325yC5EikyqxRGCVy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdkRFoN7pR7fdayFJhzc8zveytZCSmsYuj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdKwPYC7efk5uiQc2TNsuMqaw7jbxka51e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdL9AjbQUrFNaqkM722HubxM1hCYqLrVjV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdLRKevQePqdfFEGoCVzAKQyR5c1K27D2h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdLrQ7RRerTWZ6fpuwVYRXjwGpt8D4LCeX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdMQeWC7QNntLR21mxaYePjzQJjA8qdkK7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdmV689AoD1Ww57Es5WupxWxX2eLKEzNMY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdN9GUVLi2RtykH3N7axGcsET1RnnMxnaJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adnh7q5SCjAEPFWJJp1j7Bni2vSSMcY2s2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdnJCXckg2KdmUigqW6rhq9CodG8DkLpxD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdnVDg3kS7VLPQovHAxNs9JCrGCSonuDSF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdogcECRV9bqunwzhAKwZY5eTcb8gAN97v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdojyuGW7sCivP14XgHeQVfAqJMukd9d3B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdoNmf2oeuboDsShtiK62EtSgcA5RRc5im") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdP22aez6tdu4BSLXvEjdcUqJci5A5p2Cw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdPGoxFHwxkiKn9cvgVrMRQDAs1hJvLfMW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdPHPRiM6Dk6cg5tBhSMTeSzzrC3qf6tod") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdpMgXppAey6shLpC8FfzP7KQYVCnmnEV3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdPTRu3wuy2x4G2sViD5kT8o9HickCcmnC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adpw2yzsvq6zJsxKqWZRuU9TzQDozpiMQ3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdPwUySNvRw1KRY6xs9GiwVTLZNtVEqhWp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdQ1adYiFkB7VkPo288X5aGToHdfXoWzqM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adq6RT2UCV4AZMuhQJKbXDYF8E7dqgMG5o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdQ6vxPM7LSzXVm5F7ZYNJB1wLBuQLjCmm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdqGAMzwL1Ytwk18G6yKTzNKaeZNYiNNQ6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdqjbUkCZ6d7Zp36aRAm61xGKW6aZREBKR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdQMDYCXdwRkjMK3NTtwzJnUMjg4Fmd7Fu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdQWb6qmHG4tfke8LUuJ1u7445f62bq2HB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdqYFjZMEGYoFdwQZqDfi8UA15ThRWwPxf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrePdifqiihEEuR6nDFFaCNr7GiJf1Npw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrmiH3bitbHDXaBkSxERFdh3bKACrEJs6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrmQoTLbZqdZMhGNV3hsMHeoVsKBJYqBm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrPhQcR2Dat2UrNkkSr1BneQPDf68s9LC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrSsZHbL9JDWgwcG4NNXQr5fhcN9sN8wa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrtKAYUwz2xrrs5LHDyU7jxNRc9FEUb9W") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdRuM3SQ3nABmL3i8hT4L4Wz2CnAPLghJq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdrzXz3FuRaBhLCMyUazuMuczie7L1GSFL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdSCzLqic4rP3GzoEhnQrzgZbJKXS9Hxfv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdSGtk6Y8cBy7nabYRtTLnmSApie8Fe5xH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdsTXaEeAs6EhkFKJdB5cUwTuu4yvTgnh2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdTjzDS8i9e43d8EoB1KwsMS668cZ139tX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdTMQG6CzVArA1SUk7YHSbWpdm2NGkQMhV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adtn2Y3bKe2Q6v53V5btMo11tR12dBKkpU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdtQNLo8kmVSHP88v5hW4PxbRw6zcVsQog") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdtW5aKN2xjgF2wcdT1mHkdnrmzNQ7SUmc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdU1pVH3tWgmW3wumKbDdaqCVMzdq88v7V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AduPF9UtjiWZcjNqfWPi7wHAUDeS2Pny8H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdUqYKwnKQ7v1pvCaN9BaNp8nhudnVxbQa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aduywg1hc6fCDYfHqySpTr4ehvPNW18DUx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdUzdQWTxqefxw2ZukgoRNvHBtTfZ9zNue") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdvD2MNmdfUxMGmapNwD93UZUCN995cHV4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdVHp2eUDh2GR5RqYbmkQkxfHJtaCTQxh7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdvKWA9Rf6pe3niCvjDZKZcBTQ6QiDNEtR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdvMHBfny6VLCUrZL87sUsESCSuYdomLMU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdVngGwua9D7aSYoqhhzgbysHYvkM5wqB9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdW3HWW2MSAoUhxCchZVGYD5iADw5t6J2F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdWgMKQc1Yc8DodxsTdwgksfPu5P8m16XU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adwrm1FuYVFMbH6KfmcWyLnzNoXDHjHpYA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdxkVTvSj9ve2AZQvgR16An7QmnqGG2EDG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adxm8rDCBxBvVo8vdqVmBjMZadhg92Xrxm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdxPRnX4bx6r2Vk4x3FS4UVRBZX1tQa8iP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ady3Ux4TAVRk3WV4Etw7vd3Sqrm9GLvQJC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdyhVBQkYZH31vG8z7yt8XjAFrMLjwgiy5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdykgJ6xodiDXVieLbqHh4gFcaYx8nJVE8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdYL5g88rCnt4dML6bP2deW5jr4fenqa3i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdYmoMkKkz5ULNwkVnN4rdu1oJPXM8NK1t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdynyWfpcVXvJX9JhtX8qBSf6BzJ2Kh5Qj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdZBfEbcuCkg7qTjFJrj7HC115Hgdap7wi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdzJ6ovaUFfVfMMMUNxmcjqXYkyYZnDZBd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdZKdL1VUs3UPL84GqYp2djhULNQWkiYy5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adzm64y3XhQ1ULSJK9fwGUPRrv7BvtszE7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdZnKhnkQaSSWEo6M4ASphqoJroD63ENd8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adzs296Mrge6FRDGGd2s6nyBpCJNpcJSkJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdzSiGi3CLWwMye1aCBhsZvYt8uFVdKSFn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Adzy4Bre4UZpiAVtrPRo2JZcMg73zRWH4w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AdzYZjjB6jjT6Zamu37GWDgGuUebahvcF1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae1hXMdfiuDGeQSweFUhxmKCzuehPnwMz5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae1yVRtaWGDQKittV59TWSBSuYzSed1wgp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae1zvTEWzLYqxqU5LLkWMT7yLK9PfNKG1K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae2dhmCbzZ1tXX55uBeizmgkRa2PqvsHZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae2MUhb1XTn8Lb7uoaV8c3gLTfXApNNKm9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae2UHqpbdiGiSWWawVXy1c75tcKEChxS8d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae2uNGasZRYVXzdbX8GCNVTLbADuttKEt6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae363zFmAmr2C9KNJFk4e9GPihxETeFdwc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae3Df2xKy49GZ8KnZLSd7NJbwhFyg6Mhmw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae3oUfEynVrudArr7BVGYgk5u8GMPqkGe2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae3TbgPKW5umuUneNEG9DY6ajhDqYFP6qR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae4vQyABZxPihs7iDyELNh1waRezFhahkr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae5f9gnuMpnubPkUxMZLbBGCQsWAS38QkB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae5QHX9MiW9nwGD9cpQoRDnbeG5etN9e22") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae5usDyQHK3YaLcLzAnPJsUpJscWB6cSwB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae5Xrk7Rz6ECjv27tfZ24sCBEZe63bTPTy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae6CfmTCUxgHLKrEUtExqKeEEj32ncyKxN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae74LdCYUjmveHdGebNeosrNMnnHmQmYwW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae7zdburiKR9pM8websrz9nQJPMhGUitn5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae7zNqZCZKVYMDT39dxTCjmc8jwcCm8FeH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae7ZVkHa1EEgANTBbCE5FpF3af2kTfVzUM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae83DPFAVfwXgGd5T2vp5TLTP517JraqNi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae8owXaEi2M2sqNKXL3e6xRF4bpMqzMedn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae8QvDWZiSL5CJVcgMmd7JwNjcy8qqLro1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae9fFoYWDQo12m1cWt5uRyG5wmWWLjZKJu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae9iYrDTX9buFX9KSKFhh4VjD7SbdD1SJF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Ae9Y3EjpCJVEPDu8KaVYMEjZN1cXbe3gAM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeA3yg61JkgnxZJ83ZbjLRUSoA96sWFQRJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeAbz7ELTo6egaH2r3xTjhFzTLJ1m3Vq7T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeACP5i5SV7Bn9XEJLRYm6t6J1Bq18Tzrg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aead23yeAzTD49ur4mbhzjHcSDw54QkQoA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeajkCM2vC1WtMRWyiYMxmuPw9onVeA72f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeaqz36AamQxjkx563FbDV133X6Mi4Th8H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeBgHwgtkaNsd3ytckNhU4rd7FPjSwjdhy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AebJ3vBo7HpsuG4FTjW5wFnF4ozN3Zqt4i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeBjAsbGkxigdrg22pnsSS97QypNHFmatR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeBYrFmAh1ufbo6fZbXZbu7mrea8xidDBE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeC2V6HBJM5X3ZJgaPR8gSrbPXyAFYMwNU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AecaMHGYiJ1f1myx4LGuAMzqH7o5Zb3rBk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AecCiDqRQbKvhm13tht8mtMJtKyKyForeK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeCdToutX5cM2rYbuhvoJjET2xtQaszFWD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeCMNReq5TegieKpncZpx1NYwv5BohzVqz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AectYNWQzmL1PGTLhp5d2vEoajtXZzpssP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeCUqusEy1of58CLgThCNMSUsGfeHHrbt8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AecwAqpwn4nDTCbP6QoU3HGeqzKwiCnTMK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aed3zQScCQzrKq9wBAohH1XDhHsrERhQzy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AedaND26vJntHBwQvQupMD3ztBjF1ZgzWW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeDbcT6hxf5Aga4DMPZidqwrb5Cf9ZK25k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AedeASCTDpWmgzBgHVxPKmsMNTshDw2KCR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AedfHc1roxsHiJFRTFUsvVZdEHGPEnnkM6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeDgSGSSFuv3d6ZhPYzQBSTDBQn8sYQGr1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeDgVrMhEK6cG6i8uwCeSUZFiAUEWY1Pbn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AedszxQRSQJe1N4Rm66vSpUcNPgPnfLMnz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AedTZF1m7jSDYBQWzmJx3PtGk6R16WNKvL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeDzAx9urjEo58ffUdXGpYqTrRXgcJWtEP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeE7f7rm1PUv8GUiUf2pXCiLJSob6WCunH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeE8BqeCThHAYZm4rsGb5SoCGtekUbTSmW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeEc74qhpRwYviadMPfs7f4j8qXqBszhUG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeEjnZZFdqfmXWNU9MUsZEiM3mStXz9c1C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeEM9ngt6DzSwjCM6kBtaSKFWoa7zghixG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeEmTFkXnZBgaoU6e3Cu8PjvjMbHjaBoSi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeeRVZpP7DdB7Hc1hjp7YHPMHjt8poqDQN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeEyYQAJ6pwr5tozPCG3NEgpW4uKvoG8fC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aef4iqnfSwqg7xz6j2bvVahyDBqBrTZvR3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeFaiLiva3CM4aemA5uNwNb43ST9CvyAiZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AefJE3w1MB6X9efZEhzb31cFknZivoFUiV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeFXgV9T3xskzUEjtsvhN1SX8QyHPtBT8z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeg9VAiU8xQFUQsHHHPmuoH911PmA22CVu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AegDeefLm1cTwDBg8ezQhkTm64rAzGVFYR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeGgjakUA1vFdi9NfBaPaVYwnFG29AZK9D") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AegRn1C13cH2BeSfZPz4pPdzns3yRVpLY3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AegtVueVepP3k8uSomqttvMDhg9egcLaCC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeGXqZrU7JuhXYMmXsGnQxhADHPDyramZf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeHGPszGcDhvw3RphXuSWHNKQsYXmEB4Mm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeHh2dojyTn2ZgCTFzs2FBHeVWdcGctnST") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeHo7oCdAfMorjD95KXFBgSYpeG24qVEAH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeHofuTC9dTPimYZ5azQxBGyJwrqHFqzdD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeHpDXBHoGgrVAGPgAzegENuuGyFGoT7df") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeian6soou554xZiP1GQpZjzjvCvTyo5WB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AejDazz16E41WdUPmct5YZsEvNWiVMUeQa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AejFovrC8UgfYRrHJTxjUY75sCp3sCZkuk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AejoukQfxu5EzwWwngZc8jrsGNsjBjRFFg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeju4hhga7DNuvNJQsiW7xwFSjRcWkas8u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aek5SzZYjNgS24PTfY9h1qKMyUfZoARVPc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AekKWiUZBrEtk2FJarE12LCRE8eJxTeXJg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeKqpDY3727Ex2BAbJjYeL2WmjDVjzrWbG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AekrwuS6euFpbc2DvUaJvc5ceWj7uRcY69") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeks3SwTFPnVxjZYhHaBWqRN5sxrQiaqXt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeKSaBz57KacT2KgyvB3FWoj1iGeWDVJRE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AekUzC2Kyjp5D2TrbKH3tLv6mQwf87tzGb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aekxk1WFDNu9TDsYay9mdLy5VFhUXwvbX5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeLkwqoh2DqZ2gobcbVhby2aP9tKBSzZoz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeLqwoYyg34iPQf41B7ozKHJqVoBpHGVCh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeLTFVvkNBVw7G8C5qXmzMBJ8RFk28skW2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeMcVFk3sqWunvRyoNy7FSsvAaTBAygcau") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AemeuSfY45QxVHVAzZHG4uHmTLBybE3EQg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AemFFp3JuQrp19rDqRDQbNqsSRtmqykwaW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeMUacLyBLQo8fQwimKV1Dpzcigroj7XBK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AemXq7tKCkbAFtuQmY2BHW1odFVScywavK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeNHKmkfk1KQ4ZRBZej1QsRia1urUzjm1a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeNqjVKSy4RjBt9hVJB1ZsmVRNWaJdeVhr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aenv52rXzZbCRCgqkkDQct6oEdMwHQn9KE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AenvoBfcCPWDtMMkNZVypQ5smNjmXiG42b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AenwFfHoQsgxi8ouXMjJRWgYsk2q9JdCX6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeoJHyYsGpzSP9pRuz7PyNozKjf8DLwvMC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeP3Rk949gHF8b73TncZu5aWAbp5PsVjd1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AepBotFUyJ94FEb85WnwS8xhT8WwPMPSZH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AePdpVQXgTazdzpjV5jKsGd1HWipJ7ybF4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AepkAejwbBRK3KrmX3wdawsUADsc8AnHg1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AepmRMbQpB9FAfvptS8FiDGqLzD1QshbQR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aepq6Kh4t315tsyuQoNLyaqZmtMXBWuicV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeQLDUosgMnQQPLwu8Rbg8daknUHwz1ecJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeqmWUvbpMF8rSbBS4o9r4aHBtYh2mdh3f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AequVZXVmxfyC4BV8PrebpPe25dR3WTkw4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeqYjqbNTcsub9MSAYgRkuRwPgFd6YU8ie") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeQZa2FQwkDT4nR84XcgfJp4cvVNJJiZbd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeR27xGJcopgaAbXnX1GTCb7nUy2wAyKpW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aer42YHJqByv8AAjYZwYpJimtVkpDjfA3p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeRagKb7fdv8qFeGrXRgHYJKGjn3VMSuJT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeS17gf3jnRHvkFy1YFFFxUpw4XAmD7ytu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeSrmainM51rwJh5DU6BA3Bhw3GwTMP4vM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aet27pVcG5pwDrQ7UkgBTHpvbLK2PWBGko") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeTAx8uo1dFdar42mCQyjThma984ZdWojq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AetdqqRYDQvExNJA9dsF7mYBdLyZQUk5Dq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeTHGtrqddET36umYu3evfneWM13dKZyaT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AetiDoEBxXuen76UptgPm2FcHinKrSkN66") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AetmxRPQVUaWE5tySq7FTsohY1GPbTU8Ao") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeTVe1GdCU4dqPT8CQgGeXe1pfE6qUQLVY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeTXL8Y4zLrJLcEekMZxCLqd8icoM2msHy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeu1MkiwacDFUCBfjezrAFvEavaagQaRNL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeu33UdeQaJtANyT1uxSexStxUR4SLCeSB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeUbbQkLPKBYxnLGEE2cbwf5NeBvfBKVmT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aeubim4mxtkJKHLFB7kZArHuUbk55UfiEZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeUbtEft84uiDrxciV2YEsE1Q14w2aMXN7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeUcVJWvJnMLtiSSF5pEJou9HMK8mBdePy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeueockipZFxD36PRAiPe8QSiuM4i333vK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeukDJicDq134XEcS5S2pxn5NzZemv6MHF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeUPPphThpYeKTtZZAGhz1WsX462PvPa8v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeuUvi4fhTdoAk91LekP1kabNmLYjx3d1G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeuZStGCrHRsbFya4hMnrRpm5EknYnmUVr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aev3id1AwYGvzZqR3u2MxUFWACR1cyg3hf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeV3nxa8erKyANP6nUJbXobmr1Ujjc1WH6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aev6Fto4FfCtcpqxHtw5Qop1LGpTqFYFRy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AevMEcAFMtduhxEX82kv248o9vMaFDUW4h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeVrHJUqSzUu3xqcqvWawrJozF3kQn77Ma") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AevSztRLxFqMbqtY1xpRgYUWsD9w2k9bPF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeVUZy4qypRKAHyTExw2UqyGs8pTCgPeLZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeVXVXbaDbTF5YetFb7gUTPS67gHDKRcx4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AewG7mTL4998Prawfh5VrCVr25bTa4nVEu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aewq6ztMbXa4Sma8LKRrieaLncZTgP5WHU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aewzbe3gooPKcHkvx1ySSXwGdLX5wk7qSZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aex99F4QuCxGnSVeqGBgCzYmZQ5qv57c1n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeXe7Z9zyGCzUvm6nFpGjem8q9KrnGKrXT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AexmL5ZRqDyUqJuhy1K2BNwMBwgWBwT3cz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AexrfY9X8xo1SQdfyvj5gGSFVQ6vtPF6VK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AexUK7PubmBihpWt1Qajkimw2ky5CefTAA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeyfJ98LXbgJaR1BmpRV1prn8UuLXsh7P3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeYG2qsHDWHxWe5aDMFXeMmuc5p9G6s3As") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeYR7vsdSNKN8VgCJfPt1p6UD7rpubA4Q4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeYu3tkEnhSopwvFHRFnZS3AT3RQuEqa6f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeYvH4r2jGHAyEufrxNbFGLbHCXqZ76pPe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeYZe5aSsB6uiowmFZ6EB2kJCGCqBqtXAy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeZ7yJ7koTqCZKJDwebSBK2iwf3HypGMbX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aez8ztVhvSujGv6XWjFDqgnG9MidF3cDod") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeZDBCAe4wXeaXX9xtPSrhMpkc1eDr7Uy1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeZHaEhPpUmKgz5BTZQdmwgigx9n86NQYt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AezJfReWTZBHPXfLZqxBKkKv3maHUDkEpx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeZLdB7rYBYzY9a32QBHYj2cxttKnbp7CQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Aezmt6jLV8bGGLtnhAwS8xQCGcyZdGouov") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AezrqAP4opJ66fUjZmodSDJRVsz4p2hfT2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AeZtRf886b2ZkPoUb4ZfnPWmwdED61QhjX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AezVAbfSW97u2ocGva1P5TVACspJuRjN6N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af1e4ygdJX7FyTdV5c5cUNGMuBmdH9d4ru") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af1ouLWWB2C9fRkbmMbjmC7jsszotLjkbV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af1uKwQjGiuD4BhfjhyyBHZnCJocBs7684") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af1UR1cbfFGuBK2Xjr3xTrauzQoUvDKSdq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af1YHnosDuR6pfef7dYREFcQduSYiPmi6p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af2F17Z48RToT2eTWyAfjM6nmASx1qewqT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af2U92KBRJEgkZfhg2MrpYHz9etJ53HA1M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af2XqmhXsZ3Dt4wbq5Dvzd2RDM7s5VBLdg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af35KC7Bi1QvikANm7uvU3FASwouNwwa7T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af4jakCzBpFHhsd734BheM6joJB7MS2KQr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af4u5gyyMXqn2TJYy53zCr6J2mBGrDdGXg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af5DMHM2i9fRTjWQHBN1oFY3KnuVTaitbm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af5pTP3wspWLKK7EcGEoEZmLmXqqytfgiz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af64HH8VcVfDW2kysFCrgZ4nxE6q9T3opm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af6ACB75QmBPvW4EQAGHACZwmVuQnCjYWC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af6Bej7Afy44Vc8gQa3vKcyseQ8iMJdv6d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af6dBodjwpeM4jeHJFnLCHArG4URhiTvc9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af6JENJJ6pGHvpBkx8D1Pmj8PoVwiNFY9P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af6vFqZSvc9GdEhXP1goMTuBc6L4ACAr2o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af71yKiRGL6BEUmHPpzf6MDJaUBoQN9HFC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "Af7KQFC4KqATbUQQx1aVPnW7DK8EyPqgeC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFmw3BJvqq3nFkMB1CoJfzh5i4eLQGeq7h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFnLMA9cydbkFmQhR1rA6cx4vkH66qv9Gy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFntkGa4Y3oWP7nYpP4sAvDuMrAxDidT8S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFo5gWSbyL1FTxCzxEQPZbQ8cQ3L3VZmn5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFo9FgdAqnAsy9Sw2kaqqo2g9L4fqVUebd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFoS8nLKfqTZxzJPp5EAUxonGyapPczoV2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFpifgKKJS3sbH8vkXz3xQ5xbpwVK2htfU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFpNn5JUGNXapY4jNCNin7tVSYsZdkUJUR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFpp9Hpxn93WTTM41rfZRLdDks3WEUv2bB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFppcjf2ohYnbcwn9dPoUrXoWRAoTYUEKj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqdGtsyDdQhbEzJmhHuj6k9UQSfGdEToX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqEbvcsXvq4t7ox1USqKYLGZZ7fYYhTxE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqesn94uKMERDYrvMY2TuFQb22ukRxLXG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqH4aY9d7NU1heyg7JkPwShyUgfPMGZu5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqNskGrHTfcfeSQqnd59raZ84cTubpyWr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFqz37vrnLTamdTqFC9BT1GYKkJPZ16tic") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFs9FBNm7obeXg2hRtGBiLmuzWUJDs3ZXy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFsG3TYhyAVRQK4TMKrCTTgmBQMd9JFYY3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFskGia3c9oMxY7RRDSpBsAtS5uMoRL33D") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFsQ3RE76RXtJdi4pjPtCdfqE8BRmZHtfv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFt4sEbfafso4HvejmwnDbQCNT39Z3DGzt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFtj1o4uCdLVmTRZAixjEFFENGeGhm5uBi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFuAprf3ZpKnBuq6UYKHEcaihZQQSNewtf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFuLurDD7yZoY9K2JU4nq8gbLnjiH8snv4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFuqGSR5HaQAFr3H8gAvVf5eXWx3KapKRp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFwZ2UnwYXHeQGgeUwarNkr2XQx4sYocwM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFxjUvvLugEtHw6J6XF5m9Pi2zQjDnAxYF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFxpkGee6k8vEPCbbsohiNEuiSCnbRx7GD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFyDUzCtG5H6QrLj9scWpywGhki5aHzwe8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFyVAUtLxcfM1is2sSHzLu79mk6NAGwUnG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AFzjLRkkgPKDmmGEvwPUJBMQKmaZgL8Faq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG11AqL2E8qiKWWDsP8BzczLrC2fAZw8Jx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1cXry4RtJxpaUNhCsB5RCosUfEVc8vwR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1D7s4jCzvCKaw3nFXECALRYr7N9yNPUY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1fxqFFaJhamhFwV5etUXh5MzrNzYPndS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1MUoEniHFnK4UnqfVhFKgHZPJbNJp8HW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1nEHvHZxNHExWgGgK5ZKSpPAdPBPMsDQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG1NnrUXuYpnJR4oaRUpk9xWkJ7ZqPqfVi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG2CKKGrZGcM1UzJwu8PiqqCbeF8xfpDR6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG42oyqCdH2c5z1o8XGCSJBCbgmVAjjpBL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG4Dh98XEg1pf4iyzD86x8dvPk5D9CqLC1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG4HPKAwznSsQGnFnBEFiDAxsGQBpaa6St") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG4o7VgkrKwbjeZ5qARxBsXzNnP695qtC1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG4PERoTCWzaS2q6SMZRbFaaA6mGWHDPJP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG4SSKSv33RVoqPGGSKwnZzHPpZYZKeHqu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG6ebbB64BmdbUa6mTzM61PCosarEFwMYR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG6f3RkETJVt4LdHAK8yKnkfBybHuMMbEY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG6oGdzuNNEuQPpoXr9X34uZjRL7XgJ49j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG7DiqkzLG9TWVwee1SuKA8PA7Jz4SNMHL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG7P5918cmYHT2RXVTUqZc1DgpCeXuxXmx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG8j6VP1geiBiz7nSKzKSSSkVpT4rVc8mA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG8qmfLqZeTz9ea8SZfdKgnmiw3M5dRc1B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG95jXHJh7kGkgFByTh7z81Yx3tVsX5ia9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG9DjNSnRZVrq7dqciA4Wk2fpFBF34j92w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG9yvA6NK7tfniqM7eP3h35FDNPErAq1TY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG9z1c3bjv2LgbsVDVS35rHZ3KtiuEqSvW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG9zeGpApNiuLkTVLJaokfrFCPb5KRNH6g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AG9ZmDwdjRWyqrrsvgNNsXkCq6PLFA1Uta") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGA5XYyYSL8ASxSQLKHLnpLBQkusrsYsn6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGa7dyLu6gKGqpYW5KGd4NzL8uTd6tVRNk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGaasJTKfb2RmZAqKwYK4Mr4Jz1fDkKrbM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGaFyNq54nJdzyPkVHb5iREmu44wg4Libz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGaGdxRGwHptxLD3hkv2dCjQr2JB6FoVdy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGAJWbYDvgYYnfoU6AEhuhsGRxPUr7xvUc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGapuHzxpygLQLXEKkupxgR4YdxSgeiyGF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGb8LQreMpgPNkCgPqDPXFbW69xkuht5Ab") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGbbpDZtowFU8uNrZDxv4kCXmrXxjYjuAE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGbBUUP8Cn23ZCtxabKhi5SBQRcsCzzWWt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGBdSwuBL7t26auEgbMT5uVeT2FieDPRHb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGbj9DBk4GeYPWoNrBVyxR7TethzvsWZdy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGBK697CAYQyHs3h1PP8kRjDEedhubh3Ev") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGbP5R3fZdc3cGnP7yYwLkP9Um3Ldp5SBt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGBuckrE5BbQHzbJEmmYdHKGb7bFBwtTS4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGcKSpYNuJ1RAp6frBRm9YujtPYHUmbW5q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGdceCSCT6kHD4iuiqEqwx2QMhzGTeVXbt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGdigbCCmY7oWxNb4MzDw1gMVCfD3WCKBF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGDky2wfk9zNDBEeujZED2GTxFexTkod3D") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGDnbyXy5CFh4pKTm1HneusMMT8xpzJeZf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGdrT1sdtp1XSWjsc6VzPwLbWST2yjYRfR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGDwPQU38y1ttHnc5YuYR2ZqSrbsNVzWC8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGdXaJBbiiTJDoyyMZi7Gcevq32ScrMBA1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGE2yx2XxAXhsiqAsPsBHVHcd4ZbrXbusr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGE4kcDfeRau1YdpYdsbxpxwAAaQendLKq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGe6RnEuzMirbHJN4fecYPALT7f9GSYQLi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGEfPkcsqEsZVsBA7xsrom2herGjWjh9qb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGekADqqxEmjmo5TAQVyYLeRGAwmbhF1yG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGEm6pzqBnhM9k8ySWjqdf4o6hEKMxwqMh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGEnWEVKwrYQGRPq8Q6ZmK3TcDaT9CdDVN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGeQUKrp3PSTb1BCFPuTjTudUVjQPLnQdc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGEwcRkRWqPQk2iSTg6pCYXHoEHbZXqKeu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFB2tCttRnNBvFzUpyka6ZhnNk5BaqDqP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFF7Q8gkMbCeH3AFzvFk4xsrYjDwcvH9e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFgRmzVfz8uVXdqxBNDdawo1vJ2ykoGmw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFP6ApUvwi8MkKNtSZScaGM5xgh4RT6XZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFvP2BHfA3YgUH6SiGmC74eNVDhmMtLw9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGFZsAD8zuvN8qEetmoCHkZnmucuKBbiRu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGg4wyuBUywDVVZtoDkDne1SgEy6XifM6a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGg7c3Fdeo6Fm35DQ6zmHQGbiVUTKbXdCK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGG8VqGksRBm183QW43LL4Ex9yuSxWe4Kr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGGDS5w94HP4kysgheGTmg1PeTuyerw37A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGGFSAx1nTDqHp3Jqfr7qR65rzaJd4VC6V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGGJbLiCjLEYRRsFSasyY3vS3BAWMpxrcG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGgPd7DXPfvWX195PBn2ahrSobchrAsLqk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGgryoTD9iBzsv3rEYfQGmMc1ks2saaaPH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGHambSnuBvmW1wMDah8GgEt2BqCHm7B1M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGhbBB3C7dBUvfgphMajRVbeds1G3Wri4T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGhCjgNqTDTYMYLhn4EARp6cYWqe6sd14X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGhcMY8VFeqZRkmXJPtDieKMJrvdfUd5eF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGHxBJsk8hgFjX1jTr7ExiFWbZD7Z42qnw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGhzN2AgRm1QHYFnZnk4Q1tc63vUrwe1Yo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGi81AP6ZQPViZx22xX6X8KiDDYrfxYyUs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGijC5DHveGcKdpyt6m8CLa76we1Nxe2HM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGiJcUNVVTW5NRSnSPLfe3QaknfWUxti7R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGjcFd9gAPicYP9vHLphXtn2R9dCKWmoPr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGJkicsMtxnA6z1cgeHaaHKLUNixiRSEuY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGJvbrdN2PGC7j5YjrWYt4BzFxH7MsSo7a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGjXVpYGrj4ReBhorNxK52t7vhjD4hiHWH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGk43anxv8LmYgZxrk6dT9tyUfoYJZ6pHu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGKcxDL3SXZfeQyNi8Dn7XmdD4tWvpPXJm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGKeBvhvk4XGJkeU4mDTjcGjNvBBimrk2N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGkjzdDxHY2Kk2GLVke3ThRiWmu6Rxfvh2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGKSRAhkfYUGGVz4C8yxTsMFjtsoB8M1Hz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGLiRiMQ3UBomMAgHB8KWXkAzZPyKHyscs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGLyHp4Q3Cxk1gR8J3SA8GLMBrD9nFwzfF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGMdYPcw3yFNRYz8fUSdVXZpBkwfqTFuQw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGmeyqLQtpMg9LY8kvN5vF3bXvpPArY64V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGMnp19rLupeDm3mgJs9VS9JduC3auHdHS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGMpFah478SjsP2umGMzn1gY6WiWw2uXeW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGMpxYqEPnqJxu2KBS8DX8opxLGp2ujx1Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGMqgrUmmqDTYH5sfwjAJ6ubRha6B5KKUZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGn2dQdFr9kRWNKsbNi1JKvGaYipYZat8N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGN4Cgd3DxWvqpF8oxA77G1YkJ5skAyoXp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGn9J1nCpgate9wYG8e9FaEadS4eyoAQm5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGnhgMmrtq3M1J73fxr8KkeX4dm4GgZEdz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGnMkBgSA3muovsPYx6pcSbQDJ3RzmFmWx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGNzfWoBw32RVzrN5FYBsFrSGbTSLNEHMY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoCXDrKv97f8iPMBHbyFKiXcim1qPAhnX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoEdaBmYgqsDsJx6Tf5t7ZVnRVCdyfCoK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoFT83XeHggQXugRF8x7f2BeCjwnNdYSb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoLmmzB1ka8ogCRVnMa5q8s6JobvoVgbQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoqer5qSjcA4HwdRdxpf2zQcHUFg3Cpdy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGoR8g2ozf5EbksE2nxSwwXEubVJbHaJKT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGPignGCXUz9NaiviWoRUoBvYJpaiWu5qV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGpiWdCnNVxEhak9cp6pXRML1sxJswSy5j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGppZMMGo6S7TUAK18rgmSefV291s6g1Qy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGpqiWBreVhdc9LuxeJKfmb5E48zJAc5xL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGpqNAYF62X4cfqGWFJiAVNLLD2f1487vz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGPs1VAvz6HMqfru5EtLTGeQTquyxjYM7f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGpzH6czChQ9uiQDf6awZ2WcPx65872sXB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGq6SATVSG5M9w8v2YRKmh86sCZR6tyD4H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGQC6szX3vVHtAvEbxcmw8Ay5Gai3D9aDW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGQNumPvvyZN7bbUHpxz536detrsVcuSSU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGqqSMi4yASmWE2jCXcCQHJ2pZ6fD7t7S8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGRaLX6gAQ5toF6CkN9a1W8G2SkC2oXkHN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGrEWbpHXB2LA3Mynxeagnqfq7uNs5FcxR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGrnXbBxfoGRSjZM6CEziD6EG3sy4X7rwg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGrWSgeUqBbCLh7Z6Kw5szpxZS994D9zs9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGsEjk3stwAtcjuetsP9asMMFSuCgabBCe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGSeoHs1JxftT2fzVcMzgXuHJiye5n6moq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGsfX232gKxbSgrPdUVELf9B8dGxJAPVCU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGsmrRsix9x5bh9cBfFVHfzYU9bfT9sYLP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGSnEaBDGjwzEod5x2zPpxchitggkZLow6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTAS4z2Kb6FbZg3eDE2GeHoQyETq3S9fP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTd8kPj8DguZJ5Dy7QpfLt4z7bZJNn9XN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGtDsWgRhQpS5WCfYegTeD9KwfjDJcLMnZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTJpBCitVx2NnpvoiYSXqEUwQ3PQLGfQ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTkZNaFHbpjPhp1oL4iujRcsL3LSpQSBf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTLAjHwmrT5DP76ka1mszPf6qw2tTznC1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTU9mZpkTn9QyY2A4t7svW2wCreYpPBvV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGTVJpXXn9poLfodHJr2aNFrv5bVK5FMtD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGtZrPX21aSMp7DhWNeJCyHgoSJVGw5nkD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUHdLth4GBzK3Qp7M2G9M8P5jmd9k6bea") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUheqpYJaYQFRqCX46U1bzTenKwpaR7wP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGujPmAj7wn3tV7nZcsuu19yzw9qpWEaJj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGuN2KSMBjBcNifkbvcDx4YsEk6FX552xD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUperFksvVQ2Z9cCoLHsiY21t5JD5XV9K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUrP3CHHdpSesLXPfEfVmjSZBkSzodFcU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUWQrZA5dPRW9KmMX3S3rJRJz86JAxRQC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGUZDpapgEguW84NTiF94jABFRdiJLp9q9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGv5DDZXi1RyevhKLFUwSAzamNz9EtDwLs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGV8FN2nPV99nSu11WQ9qJWEDrKutPHwkG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGVAjAs1SXDr6oWzcJhGoj4X3XsrbJedpm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGVLoMwLCfdjitoag15d5VL6AB3CnHU7vL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGvSZiJYBjVcPqACQPvANHJTL7LXswUkeJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGvUihse3pcgci99nKdCnwPy28ksZj3qNH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGW5KTs9X47KaoRC9k5nyh9p5fD2wEbU1k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGW8yanE6wBXH57JHFh4beKZ5MiM5soeHL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGwKgEZ8hNdNhHNTo4BoEbcxUVWYFXsWrm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGWpMZr8H8u6psvHBQHGYUL3mxpnoYJYeh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGX3UVefqGxUxJZG9YKHpAVxyWQv3eWnWr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGxCj3RnMN7WtjaQMdti9sgRAmtJe19uhr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGxkp4f4Cs5wsSg8Rzzdjn81ebTbLWHuaY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGXsoT1bWiggxNyztC4dgzReZrzGCy6GG2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGXYfbBR4cYpEz3vBZivEcb4qbbRyAp6MA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGyEmUggEJutdvdY2spZeLiEjBG2YxDA8A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGyFLCT7huk7CGbQp34baLULXjFFVtdqa4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGYGyudJpZ2JA4Giu8gWWkJisFoddWarko") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGyRD4gXt8VZSSRWouDuVdA9D8G3y5tth3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGySKaFmX7ZEXFNe1w3ndGbkU8keo82mQJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGyx6QShjvB9reSAQ5gecx4mRSsEFTWekn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGZ4c5P67hj5RqV8UCjANceNnW8Eu8T9xC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGZ7EXxw6xsanPBK58CihzwWqVL7JTozBa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGZHFBUjgBn8DZ7oK1P3ovBvRiGrMSTM8J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGZVKMuPxLqNnzxGJusFg3NPkKCs38hRgd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AGZynBKpRtXLw62C2M6AvZTUiyrivCHU6R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH15Y7PTPYCLcVmdZPGXApWELW2BLrCiZG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1ejZBRn8nR7PEMZdiBBonivTNMqEVQkb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1muw6YyLTe476HJs7B7RqVFEJgzkRSQw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1pEZ9FhyhgAdiP5BsDg1dogQvjUDFsgo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1shmvdHFsUmGJsz6529SkPDhcrza5Yzh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1sk22PywfUfdrgffLuwaNm7zqoB6ASrT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH1VVH4abvfL1SV7FvFJBXVaEUE1QE5SfF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH2Ksuc75zpEBh9JMUJsFrDw96H5NK3eMy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH2MVuJG85bT4hfYMZ9SsJ7J6NL4Rc3dSH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH341LMXqaZmYLGeQ7VQSAhsMXcpjFba6E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH37fCfNvALceRUVnnoAP6vp21QoNA12P6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH38bLuJ8c936hQEmw3ECbNkG7cwXSKK3o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH3ENq7SXMnUNF79ZAAvdujZ4MJriNBQ2Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH3Lde9tuw3WNC2TDZ2UCUavnkFmupeVfU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH3mMAMxHaPwfmSdLoPN9CwxZnm7NwjAvd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH45bFYEcPNvciV6QYV9gGsbcq45kLSD31") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH4fRAJYiYAYvacj54YQqU9JUwjmBm8Rb9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH4Mzv9c4xgpj4Aei5pM25NAE7wZLi48dU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH5ffCZCLY23nadfZUKLT4hPjq2X14Ncfd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH5hU4wr6jkYMk5ZtJWvsx6WZg26xLMS7F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH5NCP3o85kGZwFhfU1FwScj3cXc5FwJ47") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH5vZrfNdQ3pLE43dsy7pT4pWxjfqiRHVA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH6DQtXqQv8euimh53Wm5jsKJ557q6P3PQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH6hMc8PuJdMYMKL4uUm9PupsGQA5jwsPK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH7aHrLb7Enxp8CiM35wvpDG1hDXCsi39n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH7h2fQzN6mjy6ege3LG75WC4KEb4Rv3eF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH7NMszB8TZv5mSshEF8CEcSnwkHXjtFco") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH8H2BV3TwaP3d1z6avefq7jJM47oK5Dbp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH8iNq9NnbbgbEsB5gat9jRXzxQ3y6m2An") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AH8mpCADVAYRcghJ3WYzW476HU2FBFA4ew") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHA24sCrGj6CtuHtVjNDY1qKDUMtuiGXeP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHA2RfvoKsGS6JQaZ4ZTnwxzFC3SbVP7oc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHAHb1sRpdEqhQ9b9enMyxgPQQ69FMhnjm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHAMYYpxchf2KKpRLFyfcK833pRQN5qYqp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHApyYpmm1nQtAH79F87xWytoPZsVtbrwq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHAuPtqVa1VAQv5XpWa1Wer74RQHBj1xJH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHB8PSXUE9mX6xWgxM7UB6VDcpmjrupRMb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHBCXhkSpD9cbE8ReSwqi4BnK5ZMu9uzJN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHbmt7k2Lmu8UZ9Zp7HaEzuo9pvpWTtaq6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHBoAnr6GZTRx8o5R5wyWAFEekxZUcAG6C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHBQoTzSH8x8fE1dXUEbVhqs6aFop4s4UB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHBv8pW2Y4CDcAYMADjjmRmntinmpSxMUL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHbw1zmkisAwrtYHvrtiELgzVbsddMAJFh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHbZW8Tn48jFyiqFLopo439dCGAqHAyFC9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHcf8qTGuYgz97JnZEjDBBVvZ1yEw9632i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHCizBCuAu6MqjPywtn34KpypVy6c8ts5K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHcknNQaE5evk176yEVdnTVi4biXMuQKLz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHCmUSxaTnJXFSyVXj6pAV1WpVW15JBsvZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHcsBS371CDQnEkNKik7SWxQsr8cefQRrS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHd1ggsRgUkNzabY8q1PKx7ENDvFivNPQM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHd5K57oNnfkrED68zxjKubXv7WxGTajGr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHd9bHoKqCw9SKTGGTvWAkARxCgLmGNY2M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHDXJDwch1YA1kkA8pfskuX51SwZDwmpAb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHDZgioXaADCVcxB6S2roqxPhBXcNEiW7v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHdzmhpNcf86hNbFEdjGfedcW2isaXmNxj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHE1AoCRqUJTx2fimCfk5KWqzTthd11aFi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHEcircCs9V16GkfD39s5PUwk8QCGNCfun") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHeCrjSryTmJGvJC8tkUGTu2KhtAQ6koE5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHEj2XpbWiVsRjiN6njxonCDiJ56QVg7zx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHEksfFTFsPKMtGMKoBF5yb6H5hHWjG9SF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHeWNxaN96XwBxxsv1XnubsKBmZgU8CR6x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHEYrAZk6BHSke3gmLeesRZmZUEc63JjF1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHeysEFJxyYSi6XiTZJyLwdTicxdCusPW6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHfgyWwBMZkc69RkWVdMPyt9V3aifM4jFT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHfHhdymzJepSqCHvSi7hZjgm7NPB71Vq3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHFqQovuYn2jekhweeqZv9zJpTq2c1SRgU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHfWz6TAtpf7KrxnSjvza8va3EvY4xqNi2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHFYpsVbqMBpSdcsKQS9AEHZeWpy5ybbgg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHgJYy6cp5ZVBBHvLkMuynQErhPELAyGVw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHgLr3Tvcsb1gSa1vqGj3CQdbh4E6za9Jh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHgPEnzzGxPsnM3KDaRHR9HzJEUCZBSEUP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHgRH7Utuk7uXqQmMgHHtrL8mYf4MCWhea") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHgvu4inkP15VStqESP4PAqpw8CXgc7wPh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHh5g5fCodQduJ3iLjFycxrVRm2MoZo8hf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHh63MuRgt9nQQQkhd2jkPqKh4Nk1PJ6jt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHDdQV66JGwYto2nksRFdAKd7k7bLWbxD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHgpKbtinBybhNUqCgwGEqo3oMXEoYnVN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHKTnj7tMA37E5SFC5pvb2zwgwUDjQLQn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHKWM4CRdcRnrN5LB4js2gR1ZPofR1wkN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHm9ZuMYC9PSEg53DCxnbsC3PSZ2ANq87") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHhNBnK434Li1cc1fTTNWxfskpQh971G8G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHhX3mED6iSjoCM94ANj5ndVmuj45L38TZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHi3cGhAh29bQiVBk5Ahz5yr2xDKjZR6Gm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHi4cn6rWjJJcMjSYF45D7ojbDcsc2weL6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHi63kbPXEkGL7k6dP2ANdzCGjKTq2hHPn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHibwGjasdpT3uf9a1GmiRDSaqcgdB7D1w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHiGpBxffuqFRNAFDVvSJzG9eUY3KD1FWJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHiHwn7FSAtFoFTK1axukX47zDAEifEWe3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHiMgh8G7J9kF8E82HhSG7GaLvwhnQC9Mt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHj2omzZQ3xcuapRgAG1AfxSbTDrZShDUS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHjBnw5tCBNCsRzMP2K7N4tWSQHZJZTVcU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHJFhG8n9q2Ga3kCQXV2nyUZYUL3RMsiP1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHJfr87joXj9BjUZZN9yCuJvnpbHXa2PT4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHk2sRnvnU4D3gRvJ7kxTFb6oBLmvEabZz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHKcBoWDDPT1jXsnn2rwwdMT5ixx1NccxQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHkdMEAKUcv5JcJPR9Pn4LwwtFL52FuSsi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHKML5K3ccKaf5NK3FTgdDiGvBNWE3roQZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHKpTjNEHfSyVddRWNvSPqqCHXtzgk1Fo3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHkW63UkZqwWAthb9E581cZCtk3WbgpghE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHkz2GkTYzRcZE39X7LiU7GGEycjVfA9kG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHLKmCvZPRVFv5JZmKb5sCRNaFuEBSJPuE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHLNroQUALbNnVa8kXY6royDXwcjGd1ZTG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHm2tR5zUzHvM27vzXwhcbky5s97HWYLEw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHm2wvc9TARwKUk9QPF9wQ6jWi7YwLwZWq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHM4yyqkJG4EQJ2uqyzqcnGEB3pS9AmWBX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHM7cewJvP5aWmJfwkL3ADrzDStqrF8jHb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHmLgirckHAc4LQhiVzSMz7XmJaTnygYDb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHMoK8N1WoxBCLYkc5QpYtszAcxHgsa2Tb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHmRdKZ51yM9Nd4U6PKCGFwKMtPWmw2FRq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHn17BuuNTjBbH9LSikfy3zMsR2eAGZWGq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHN6VNPajwPzjN49pVvxjkNPJMBTTg2VHi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHnEGA483X4KZ1k1ZWxGPXCFp5R9fqQt5V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHNK3219ZDNsRqZGkSazrUDcQ8fmru8ru5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHnwqEENcnZd2fY2H2H3mdarvVarW9ZBQN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHo5oYqjjW8pm4RN2Nwa9rWgeZe34HNRSA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHoFyRoFWgk6aEu6S9PCya2qrPUPemj1Vm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHoJBToiDWF6F91jRBMTc4HdDpUNyH2uH9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHokHtgCxCe8ySMwVK2hbxCy3rHAJimj6x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHp7neEzP9YRGXB8NvdJToPMBuwu46DuAu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHPbJjudEyB6EkpbA62ZQeohXcvWRVkNFx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHpg22nuz2GrLs3hpuQiZCkW1TybZNzShj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHPGbFQGC8TM3JGgaGtoVkRwVK1GNgrJuR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHPiLhc3MK7zy2GuYFZzTYGEMfr4W93eFb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHPsiozsdtu8udKHu7ARc7ktQnT1jDh6KB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHpti5Yfc3a3BThep62rgaeJNrrJdVK7LC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHpWkybogbNEaJ2MjcUoMHFD95kLWRqDM6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHqcSvVhCpXRhiXLAusihBMEAk9He5B4YV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHqGgFbvBuykFr5HqJHqsQBVMvZyDkYSyP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHQo2dNEe3vXHEkwusKbBmbeWrj69fBb64") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHqPxgFXfr7DrXKRFJBgAJGXHkdpigfBNz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHqrTjBimG7HMHun3UB7XEmWa2GkkyyhTw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHR7Z8FQ87RVXYnbog8HVMT2F81QSRthRJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHRdYxx8TNqUdfQxDLCZvnL8DkjfyRrpNW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHrgmCsWB9jGSH1i14A1PHkrzjAYhHoBuK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHs2gQ8ojxq2KNbQUNsXDgWwVMRCB6AHfx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHs9zvwGBrWwRYcsVCciMtPdWaTUHKJuu4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHsfsodrCyVtTXbEVfdLRFnFhsKTK72vKS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHsLDG1sPQuUb4skE1JhPMCZ1f7CnkrXwZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHSLEpvqNmBuV9YHN8yystBEYHMucirEjy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHSqivMM5zqM5cEsAZVAdxSf2GzhVWgzPv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHSUKybnBp4cFo38H3NgK2LWsP3FcBt96S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHSV62XjzLdqboZGCvvyRFKa7vo6kyCPqJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHTA5N6BGxyt3dYQbiEBQosi5Fu1KkjNxs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtFeUaUzwqGFzTnYc9yts1gPzimrEH84F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtGYaDtfZuKSHzzL8oCQk3JhwkgLm51Cy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtHqj7B6YQR78GDW8wvzNVKhKnQZJuJzv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtNNAhwfqLtFLRKfsU9z4xMjiLQphEY9v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHTRp3vXaX8TS7fv69qxNWkbfdmFVQfPkw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHTSuKshJHhrUnZXG17v33hwzoA2qULnrA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtU8SSjJRryT1cMHVZnHS9h6okbjqvrQU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHTvUkzUoXFatBpJXoUpv3t1Q4R8w2XWuF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHtvuP42Afziirgf5sqLHghPU5ttE79jm5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHTyjvCkcWDRaPAKtjZSLtUJpjPxk51rW8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHuepSKQuEcBcj3Kbq4YG7AutuK18KtCLT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHUJR5hUCjmQhmQbtqVVkpc7fMT8wT6Vin") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHuKqsZw5nSA5EyCNDiMeDzEDrxTiqnCnt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHUmFv9HA6bZYLerVJMbHdm2tU8PLnZo3Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHuPfpLYBggWkqLkKQkuwHVJAt6QS355UC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHuQ548NXsN9BaHMjDLpYKYU2vUTSbpft7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHUvQ8GozahvABiyjMtqf36AA1cu2DWCrQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHvFAU6NHdsjyg4aAFpzhVbvKDnp7uHgdu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHVG17s9Prm6SUkf687HkUUwzvWvKrXkkw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHvhmWEZuAFhPGaTyiBShNVxayBxebTpoF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHvL72EgwJQ1f5T5ZBjAYNbRFcVaiswSYS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHvQELy9XGnFs5vjNSkjbUTTtgjGjuBnNb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHVRXCtpAWrhJH8AtJr5vaKWZge4drhcDH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHVxoJhz58uNLj1233PbKX93fm2eFwRTYW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHVYeQALAriaPpgg91pYuQRY6QirXmh6nU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHvzUD1DiYh2DMpgjcmputqkcmqUxVc1QS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHW1UPWZxK7Ei4p3QhiXa7gQE3F2ExoTzx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHWLBjciz92PYTSi9fFExvjbwzcC4WBfPC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHwqYX2t8AWFVuGAs5LDUTjvixqgzTPDKZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHx6KDzxPUAhWn53QCZbMbYp43rN23949H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHx7C8X3gcHZtrDTAkeYAGTCNZmaUMpPqH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxcT5hapYkBAJm2QoN867p5JrK86bMDhT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHXfkg5YHrWpYUpgfh6D24oWvnqTjMMtwc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxg8VtnDHe5aTsBjgrcUuC68VBW8R1pVE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxj5GNMp6YND7Z9AeUV3oH884XoTJ1Qja") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxPPWLtZgTQNkJ6NujwBkHRAwXpU2YB1L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxRYGPBKfQVwnqK8tVgAmHnBjCzpQSujN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHxY8odkM1j8zs87FqYWCy9UDZ1EgemZm3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHyDsZ5XuJZ1HLTU6GkD8JkCbrG2RDK25r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHYfGgp5ySQy3jNuGfUNNQVQAMLvqTy2hE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHYSz7XCzc2ef16JGBaQZ4EU9wuLFWPG3Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHYtmMR64pY6ypVBr1tgyBGLTrmWAxCi6n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHyU9wDo5F2aiecv36bBVEyDggPhXB8Qka") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHYZZ6wpQDLA4dMiafqp7pQwxt7XcDfp36") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHzc8jYegPNZbRVtBiPbthQwqSD8LGzRaR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZe66FxhtbhCEkjPPaAka1UE68eKKG1XV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHzhTCctsycq3PMcLPrmusoV77ZkpGDJnc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHzHUHpy77XAcDtrzgeA3S1kvV5p7VoibC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZiA99zdjGvUFi2xtP7u17j98EdXi9KfG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHzjT1mBfzG7gTQyzknL9c4rutVafjKLng") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZLqKvuvVGYQusn1mibkEgn9aqdWtZDKB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHznC1uXHXwfM3NqajHJddrMAj4YbiriMs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHzqfkT1jtXs85aKY78oUteLaYnJrofkZJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZVcttvmSyhgrNESnDw8ESd2TenK7CCBH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AHZzURMhcGiJ6WLAZQJrTE7s1mDJt3fH2L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ1BshBEHEX938fawmZecdQ4zCwrXvYEHz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ1FuUEmfWGE16fZA9izZLCxUk93dJdwJn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ1TLf5QDxiqGfMYkzCHbaPv5uSbcHQwhn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ2CPUg7S3JFb8DhPMnN1VYKfFbXA72bfp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ2u49W3SNFXMMohXFQK4VX4aYwddCCHdx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ359nzBDUhp6NNqSNyvR5QYt84iRHMff8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ3Fn19BPqAhzu1FG4tawRtcBarVRMij9B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ3GmbwjBEbhSrh56PzzpXzrqY7ymRjeDh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ3Hxkr6Ge56rMSrePnunP6wh3SvZY9XFb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ3HzyM7YQmYQDMnH2pYdcJiLXCTfWTgrE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ48BZEiA6W3fAyKTELA9T7pcUBhPqra29") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ4BioeATKFYoWxo4uu5zCeWzh2fZBGq4o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ4kNsPn2haQKZjbtd1zFjhYeXtg811xrP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ4Mg9WiURzbAftKNUEp4hW1YzpcFMpVAv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ4QZchEjVGDHPRgYckJPBCdry4vNzTiz8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ4TH9w7udc9Y2azybNpkwWLVc94egyTZU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ566RBTh3GbgxspBMEV4sHyG2ZZDfVRHC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5gX9HJwdayNpbwWLmtSLBjejRWA4eN7U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5kpUVTVk8Xtuixm42y7CiVgQoCGamMni") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5NLrngsV9Qw4frjNS7LRwPi315sm5FZm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5qkyY6T4AfYaTLUbxULsDwggYzm8op89") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5rTzx4PvENieYfpyR4odgyqbnbwhZTsD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ5vBUh4tXNgJ3esUUQK7iJBYm16KfJUxS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ6gqHWztLhXkYX2gvpSNm46GjK3sTzjCU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ6nzVrVyHKeztQhy8iiDngAraApZWQ42R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ737v3UXkctoxXqpwJyVGPUrPXdXk7LMZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ799oByNAr7FM2EHB7hdi12K8bTENLvhb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7E4N96WwaVrv3k3d81PVwVUR4KpTRVmA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7SrsaefbA4MvpkjWjHaVueDiDK7LVvin") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7unfqqdufW8A7HrvNQS65VS1JZ1B9MuX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7WcXMmRMfVFMwHLoP9sZgcmBQxHaSrMd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7XbqYYm5ps646NmRXY65kpdfQtsFWdZB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ7xMNeRkyiwNuXjVUmYjKFCNfKgX3ViDL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ8ffs9xWMQEsZpVHrRgtxgtGSHD8x44er") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ8jYaKGC5sPf4THtoh7JVoGr9NTAniuMY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ8REqM73SmDHspMw87KBnj7AdZdghGnRB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ8woBC4Ci3RMHQDN39iDKA6pRqvBonEgJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ9MY8Wh5uEUc5AiVE3BWF1pXJcAUGpRPb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ9vWrpBhbJMNU4C4YtrRMqNJmvsWHZNbx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJ9XoboLYzhGcrrkVXdtyF43orM3LQX4Ap") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAAWsEcBcWNmuqGiK8f2YSNLnX4NprX8G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJABhxgbrZmwtE6oBVv9MFjoJvahD7HqLU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAbmRCJo3QApCkEsf1emWmL4akzKm4tp7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJabYUcqLYmodnTbGx6stJxduofNnJL8bC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAgdS2GEW8JxSnroE2tTVKGsBxnBAYB6H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJaGYBbTFTsZonDCnS3CWT1RZukT7kLuX6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAih3aoCq66u7CWRjDdZEQz9kNzP7cHNd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAMrC5EjzD9ibnbfd8DPNkUfdSAkBLVkT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAQn18vkrgVFhriGTd3NUMtxf77aXxkuT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJAteTeVM6qdktnbiGZsnJazAoCeA9kapp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJB41WpnMcQqzTiXneBKPAqp8fbiX2qn9w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJb4TW4jzYi8TETLvpjUxFv2iz3cFj5rmJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJBBSuxzsVH6JoKYfRsjZa87JSMjnVtnxM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJBEtVwkuedT2tQ6CVhuuRSusmW11Lc4Jx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJbNPAxy4XpouNh8FW5dhR9vZzTH58Syk8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJbspJNMUvbdYfZqxPSoEiCyEdeu2SwSB5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJBtuRnTdUAoXYt1yJA1RsjkGp7uMhEf9x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJBxgEk9ZJ43pSnPThsxPNr8eqXUaru6AY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJBXNK3R6oN2LgYqqawVfAuXnBrSvVMLQo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJC9EPu8y8ayrd4a5GmLaMiRzKc913pmzw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJccFEitzvBrCMhgPyEDjDzfJsyzrKbLoC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJCk4BdeaiZfMwoggqTXdjNRXZnWmt2uwy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJCspNnqKXQhKQTBt6p7JMfnkAALAKmaBh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJcttjgiDXEh2b3mptRCh4hywYSdw6hyzf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJcZNiQF74XMtKPc8KxpxnZwRuZKvtmhtY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJCZXn3RVdq4yTZ1NKe4FGZV7wdPN8tx9a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJD8bQJhe5caGyRre1jzXoQMnbCNvvm267") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJDFYKwz45uW511MCHXrRZPRemZkbMgW4C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJdgXTZuKecyEsNZxu3DoDYdwdzXRhJHg8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJDorwvCRDbiYmkLLZ53hW82EYf92Ho2MF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJDruqq4Km33pJPHpKicUuLrJTM5qR9EBy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJdSCwpKrwXtBuKo6ifL6GJaY2MAwD7QKt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJdseYeTxa9A77ncDPjvNSSeprMpTZARjU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJdUGr2a3uEya4qjnavZSeF5AVU2WUgLSD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJdvX44Y7Hgd9sxANwiAWTDrDAxmWXmq8p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJDVZXkK6rhg91Ywx7gWQQETRezBgxhhDu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJDyVAwMmo6RL1JF3L7FCetWS2VRM16Jc9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJE5khm4KcxkCVMt3kixPydcxsWNzUUEtz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJE5kLh3KMSpQ2j7qxhgBP3Q4bu9Px9DXd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJEej9mMUuTibnzjJGiN9Umhsz6A8bePyZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJEjNVo4zzKBq5x5SoabgB9d3EiNrQ9Hhj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJeRVW5QsbrGtvZSn3MgGg56FLJ7GyMMqG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJEUSiTkBTsdkCYp4KRVuGuHikV167cv8s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJf7UyouAvmm1T4wBXJdKooVv8V412uf44") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJfDKLaSsX4E3x2pDYuL8Uy2UFc8WA5PP7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJFG25vgdgoJbatRsrCo98tgC46NdugPbe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJFPjriwcU876oQkEV46dE1aPLRnotzGfM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJFsGqeP34x9zHqx9fNCWge4rZEaMLmAr2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJfxFKBSiueMQMqMUBKBt4KvqBGZwvXgoH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJG8AU3LLjFwC3d7j9vxo6aQWa9AfDYxWq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJG8xDKBRqvkVCx3uV35Snn8PpwJKjXYzC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgJN9TuHfLPRYnFMSCezviDDJov1Xa94R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgoALGezz5YCPX9AVL2QrSKCSbo5VDTSx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgroYH62qjdrB5AJRnfUUCH86AqWwNqbh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgUQry3oKUv3VmKrDKSJ2iKkQ2VBHgdgJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgYNPwPSgnRmYh5HHuriMUTRk2H5SYrYk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJgYqMKLYbvyAvE53eGJXCiyd7Et5RwV5r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJGySWq1P5ZiyT1UT2Vntja5GBEUt4trrg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJGZjxvxmctCE4DM4GErAhXXvbQt1nBPDW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJhJmXq5h16TCd22tWExn1RoYFRbm9QS6Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJhkZczpogHYoyVQzTGngmkFf7zEKUyDiY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJHnWkYKmKium4uvc2KRVJMKdi7o9i7Rp7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJHyekw2QLW3dtN6Kk5rTgpctQET48Bfmn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJhyHtzQLFhzRFChi8fFVwPSfYuriuNkcd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJhZkVcDcpZcWEghmqFuB9YuaFw75qsHUx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJin4dikP3qE4Mt3h8c2TcujVr9WwpJJp7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJiRwpoSX3JQRehNg3bMV7Lp7jesETTH72") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJixEbrEXyDpJAt5FfFEUzjaKXLLTnGWx8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJJ5qiCR232UHUW57f4PMNMTi1MHqgao9U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJjHUDYeavC1BzyyXx53hiSmwkzTLCmYxA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJjMphtzj492dTZHSyF5YjXkNxKuYkAwmk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJjrXK9awb8fMA3N7koqRXqDqsna6nWqhn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJJvRp7aLZH2rnvmRJrVGuKKR3p2MvMmEZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJJx1gtcWFuWeUbCjieXUBSs2qTGfF1AQT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJJYKvpW5NattjrUciSZmqMmKG1rrBeMbk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJK92NKMvFJBKWgQKAuWndPuWfN9LVGVEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkbUMR4SoAGta21mdHbctpnSFdpuGic7Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkHC4dqN1i97rJ5js1SzXeLpukAFWgMV1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkhjVtjQkT8GLYycG9js1NwXCBoj8sFsT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkTbxB2CCuHwApFezEe7Dde3kc7h49ZwK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkUN5ogU324gkULkM4SDN9oXAxGYo9hCz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJkXytipKWmKL2u1You6HX2Xv78DuTBCxH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJKZW1RtChi4UQJz5NP8N9JTdp2JwJftDi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJL24rj1CDNu9XLqzdfsTyCZf9TQbsJHsL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJL9U9pgqVS23J3WPwpQbcdrTvpR71vYYy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJLtMW4zFG9zaguA1CBoiGN9JkdHKwfH87") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJLtZKsoFipqz6uVkTYXbp2ySWxJ4h3wCY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJLY2MR4VARzDErRd782bPu47bHxaeXzcp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJMF1LwJpM5UgF31PUanBbMMQPjMkYXGwH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJMGTA934Ekw3Ehsx4n5HpKrDhLYn2WAS3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJmSJfnMwzA8DYA9rS6hJhcmdPAJe2Dj3k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJMuxhBoRqrBiCpXhtMak8oc5yxRUW3jnj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJmX6wtkAJUotyy5wgj1ucb6Fhm3W5HzG4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJNgNDYCVdjkMzmN9juGanwd1gobZVdT7u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJnhVEHdxDKuCXEnBpfXaqfm8bBSJKdSjt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJntHAjeizAQBHdP8FNAMNvB8WHnGrs3zu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJo3pq2b73zxTXScr4uLR1NmcXZwvHoTiA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJogqCm4DkGJUigMG1xiactEhPxJmWxQNN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJomqFNBRAEYKqgqS9pA24U2sM9HUrER2U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJpBdnSQ7tHSje5gSDoBUcT887JmxaUSzp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJPEGTj4kobuMnKA8M7kTrnd4qdsVyvm2S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJPKVca1hh1os3UgqSNsTYgzzSiyjEqyL6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJqc7iUxq9Dho6DxhrFZvoLDVb2JaHc3ms") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJqGH2eAt8A2ssgpiAcEN3es15xEYzhLwL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJR1QcydExaQfzEHRKB2dPHW1a6y29rLKf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJRKtwZ4JZUL6qknvmuR5FFtv9obH5JGhT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJRscgip45wiTiufJPSaiM45FNSzzAsRuV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJrSe3rna1XX3yJ6hPTjzkL8JH8JGBUnmA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJs9d4XhULdYJHxVVgV7PwAwBoNeGXw4yU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJSDHYS7aNzN9rz3svVLaDWoN5FieMFeZu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJsh5nPaU48B2FPbGtHgs5jxmNwDTQQc6T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJsHTPVsMKe8MH9FXrP6zJerWw5zJSks2G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJSJKnm8DrkS8X763zFjhMTqmbFrDZFZHs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJSqBaCjSBH6RCFbnyXWxRR6X3cB4Be5EQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJsSJHS8LVS1sQBKJ9aGQziuJgijF5jdaD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJsUKGneMLTAMZETFKg38psu39k3Svc5o6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJsVwurN9qyhuoeZPqNaeCe8GqTRr8qLwQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJSXGFBRKw5y9vuy1hTYkb8aygvUhUbAtV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJszcwbfCsinPCp5H1EBL2nV7WuSysW1cs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJTa1ynBKJ5P3xLu2VdLkhrcmiwWgRajpa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJtaxojj6RY2iGiGbJd96ZWoYzL7Gicj5F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJTD5cAXpPwxNcqYXDPr4GG7Ndn3U9RHdw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJteEX6bRKTF5gNFjUo9MSQurangUt9WPE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJThbT9Q4z3DGs8H1VaBcG8g2UYBccha72") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJtmN8hJSteX3ATuTAmLNYLR1qFTmYrZah") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJtqtJzjN17E1FUqmrpfpAjrrWcmGodZQr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJTURhcnCUjz36rMKBJU6zXkRYNCXZ8Mcb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJTWAgkfEs5jY9wgcC4pDtg4dFZV7dQEmc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJTWbrS1GxNYRYp6rDJUcbPZXQ1LNBXCXw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJuAAJyrfF1ywkZHDhjbogJKr17QLL6Px3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJuBNuj4fpyW3vrwYroreywrSasfUjuzvb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJucsJcY2cNxMZb5zK2g5AEZJJqa1FZ8qT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJUpiKx5mtNoANFDaJZEWDfYytf9AnTb8V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJUt8QKfrhQt6sCcxJks1kApiGUFG11nam") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJuX3P4Mh6hMf1yRPT2oxjAYpiJjWJSfPg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJV7PPvpfWasdsVUAea128bnoyUzmBmpEz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJVJ7nkHVD791VwRxVYn4viW3re34pz8ik") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJVr4P6TUcVJwZzP2F11cuuhmTfAAYrjEr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJw51w5ZcAxSx3F4szMx1sWB8SWt8GD7ME") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJw6qaZxytLszeUnkomfbTj8m7oMwGhmqR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJWc5UQ6gPbmAvr7iJpLubvYPPkfzWB5Ds") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJWgNSV54gbp1N3T4zk3gad1V1TkR9mgWb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJwR4yM5gwrJkUotGP2qwLfS2Ks5ykgYig") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJxjPSAeh8nW21Rz7mg1kHEtdC26FgUgxM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJXkZ9wq59uwPAh8U7jf8GnYta7ug6Js9J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJxQ9VnA9HTsD8C2CPPELHw39tnhZHzBqR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJxTDMtwdfuVUtSxuGm2c1paN92edqkp57") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJxzK5xqSQvfkjYfxzzssQs1pRpzyLtSY5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJy54mYfkhKEpUCUcdR33fhZJ3SsDpzvu4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJy6rbS2NdoFenPwHfFm2qHUVoZhd88C3c") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJyAKEZxskZ2pt8D1nDo3YnaNZzqKbVuLB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJYbfqtu9FTw9hzP1x3kcQuSNUvAjYTRsY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJyBUbXUYQj28qwSZzPPQFiagopwE9sG4K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJYfcQUpS63ELsGodGVBsQxokGpQBtVsfw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJyqSpYiBvigKZU5kCajEwcbmJSBKFv88g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJyVSDNsvFakRrV5DE1AzERBvuXZ9X3xQY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJYY6oyEZeMvc4xPLGyrkeDgAdhXZpe4Bz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJYZ5sXas2TFXsVhFFKZkoMCi9XddNvraJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJYzzBZLTEA9M6kRgsHLEg3gs1JZCRFLgK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJZ5SsH7nbQdnPt8pWcrTpRebDjUyVpWHh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJZ5vgrwZVbNKYbgY7wLbnsPAQ5F7KReCY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJzLBJzX2NguvtyZCkcNCA5amGScf5d6YA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AJznv6UJMoJFrA5ZWwDYZDnhmJRn1LSQ5C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK11VZG93oK2oDT49hdD1ULxbQncT9REgF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK1ftowhZzgjgoTMyjqobNAR1zir2AahR2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK1VrQuMxyLsnFwfoz9MfeGU528ukAHdyD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK2FW48KzvGjL4X71wiYQYKxcNX44pWfwf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK2mzz2GLVpeHR77MnYrY8jSpZgtUpQojt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3dA2tzDg6jniJuGrgX8ENAoQbRWH1DS2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3p4JjMGfZ33RcEq6VhZRm6e9sj4kFQ3n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3TbFCz2FJx8Z13KX5UFKtRm6XZrctc18") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3W5GN8xXRo7Zc85AWmyZC8NHFnuEBNyy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3WhUhYQJeBkfSvR6vSQaUDF1XtCCSjdb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3z3r9NwRLZ8NojNB4vjkXbcDoeRynUeR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK44my17FhpN4CAySWWN8THcCUNqvV6AY6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK48SmzvR5JJykd1H51mjXVKBXBkeFCG2Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK4fzB2ph9xUXAuhYjqcRJ9qq436rm92HC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK4rXL7u8QS8zNYBX56h3K5PRRkHWoxJ2i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK65akvjxkAMh8kz7pHfYLRHRf449pyrbZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK662KpeeaCDsw93ekxFR5JyqjytCySkMf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK66YRN1CXVqu8hbUwzT3jc45RZA9N4DMp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK6a96YJhZmm8Pz47SqKrMDTiRHBAeo6Mh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK6apjtgVv9KEZ2snpX6LEJLMjStoVps4P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK6Fvh4RvLXBDd8K4Vdj6pc4B2BVhAv4Fx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK71BugaBucXtwjCfRy8qBEdP5MDhQmhMR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK7hafvMyzpzuPdgKM9N8oFsCMd2iWpxAd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK7hQWVF4g3p8hc8Lt38ukaZbxtrtYq3Y5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK7Nygbk3S4pMia6i3io2gjw9zyyTg3dam") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK7VzwZqS16PJveN28eHNWMEnZrZShg6ik") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK7Y4ZViENwwVti9bFRhJ9k1WwR59ddY58") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK81X1xeYy6xqpuab2zVWfwjLx6kmDAgP4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK8FLRQXhWQwoYCLPwKpSvshqzfNp6YrTE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK8PmvHAmiusfAbMGtjcVTuaDnMbRWw2gq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9ciCkXeXsCkBAQrZmYvovGyKgXAwQTvU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9DfQ7yEouisZxR9LmR1pJCZmhMXHj6sc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9g2TMEW7mvFYVBLZxofAJmRn2V972udN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9qoYn7UomienA4dqnKhdtAWPhudUq2Cz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9XGDDDWPhkySzwxnXwC1xR6RKr35nQpj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AK9zqW6ncVRD5YZ7LY6pxywUBuuLhVSm1R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKAJT1PuoeJNjsvEwTo6XCPUzS5AySayoL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKaLnf335G22hscd16x4sXXTgVxHykVdfZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKAMgZbiEDwrtFcjByL2wqhaMN5R7xodZm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKauwoZMmPoPbH6nsFH8yuV5JYB2MHZ6YL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKaw2wE7LFENKmAYSW8rs12zCRZDsGnVCd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKBHUVVhscDudKHgqn7VK3xpymdet1gD6p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKBXTUFc5aCB9crFGB7trEqBMYowv3NGk6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKBXwUggniNcrtqzuS7tU183jKsgqGbBWJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKCbn4ow4TDRamTnS4U7AGEoFrDM4TKXqk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKcbPAQsqCTcyFjQmdW2DMq3my7MqsPjPZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKcrQDa4t8gYReFCFM4XDdkfNCsow4TjTc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKDHuxNJrVmJgSanvyymB1xxRN48eT1MJF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKdMh2cvoSaGwtYRL25upH3Y5e3Pb1Knss") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKdMiqNcdjcfuEZg9fRhgrpBn74AGFceif") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKDY5uuJUXPocjiWjpLGF9y8J3C4KWVGoZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKe3Xo53gbr6ozSPeAUdfQondsvPfB3qoy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKEkdQUgHMnFt6rkgF1s6KaPLaJX9iWjFw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKetUYUPe4uRiNsKpRUEoZcK87ZehnrJ3p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKEve2qS2ZqghozCW4W6sheCFi9SJdWmET") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKf2A6jwN8QJm1HmnQV51kpoQQEZXBgmZZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKF6h2QP8Cbs2Hf2bnhs7iphavud6sdrL7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKF9eiTfeqkkoYE6BTwc2jvYH3GcXGyEvE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKFHbbqLwAUsAduHCbFDG3EnABm2JkETXt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKFPKFP5mf8B7ZY7KgpMRFGNS6yPimKEh9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKFycC3Abay7Rtoa1yQPU1YYYB7U47tEjW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKfzMKxMeYk9asV2pNAmfC82z8x75qwGAM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKg1TYEBxJqVkt23sx5d9cLujkhDGuEiww") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKGsiS2FjXZgfX9JxZbfsTcV1dzat4yd8r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKGvMdgsQ7CjVbuSWA5aoQHqnhsdpsqtCc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKh2HNyicLwgjRfxq2Gbim2hBZx5nWagAw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHeS17TWb6SpcTqX552RWV7oWFYMqmbyN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHFD7XWykkzzArjh4RqbUnMNABkSFpqiz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHKDsY5YfZD8JWt2aieBaT2xfFWKnhrdw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKhQdCfJoJ2QoBYj8GhHDjMz6oH5N9SCDF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHqmEmAVv25J86v11PJgHyR4UQPRoCwtz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHSjZiHAJLHji2cPV9fTSrn4DEmtHcG7G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKHT1WuYdC5aKEUZQDGEv5qynGiVNsHVcm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKiFjJM3NjGDpGeVrTpo9RjwPWd3etDsUL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKiFoBZHEVgmWSfEygNpo5VPYe7Cg1Z1Lp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKigYSfzqsDBoXBGEqXUP354qPdZQVPhqf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKiqwYB9grSjA5LtKZPjC85xSXKtqBqJCY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKiUtLkqaSvMhxsVszdzHe7vyAaBzX65qv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKiWseH7i8ThyTiPhbGhYQQ7GNTEGLrfBR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKj88oSPgfKdkHMctLWuykVMavviT1V74v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKjnfBbiJMC1KwmZar7YQfpp5u21D6NPvn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKjP2NN2YGRYirwfJQFRgMrYXc4AbjA2uk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKJQDaiHf5UWhrqJMY1eZcwkjyVRzFpcvR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKkbaSkwox2ZPjfeYVouKabKdbFNjBWRjJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKKctLcRTGVC2bBGcyPCGd9QeYFH7NhGcU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKKjm8pCSy5feTSPpris8XxKDAHQQ6FUbw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKkM9sb2GW9n8k7sMJpTWYyXVTRsbjtCXo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKks1grBhzRXD7Xm9oVjSVtZ7p7beH2c9V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKKyCoUGCAaTA5xSnVWaA2WpaUE5RoESo9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKKyDAfaAnWqYWwcPYAwwtwqVCrachpi44") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKLbFc1gCvYBLiWF8FpjPMFYkci15yueQQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKLTQSFapZtmibvYRbfTQHzr37Uqt9vw8v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKm4SFCjwRfkamfz7ozcEzdduVwL92RpjN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKmborM7RaW19t8QsZXYNqf2BEcA6HhoWr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKMbtR9reBynvFqK87o9NgkqYnTBSD4sUk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKmdivcXgqb72qFgUttfQtzj7LQT4bXZKm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKMnNx9DXUoPKsJKT2CxDPr627gGSHpmEU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKMNPV2BQcEEWHGKAqLEXbobmBK9KYa7L8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKMzLHLdrdZYNq8npPokQqeu4D1UEyy6yo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKn1jnmc9bvK6CohAnUFC964yrXNck1Vzq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKn9BdFEj5Ycrh3DRGtdR8SQLwy1u4gyQ8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKNACD4TjFyfy6EqR4uxxhFkDRHrWxPJVZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKnmCyg7SVdYoXHryS1nbdMNHYEbmjfbAU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKNQWmzpqonKJEDkxKVoj15J6s6wMXMLvM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKNSqXxa5iMzFmxbHRVS9ZZYU74MtRq8ki") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKNzEAMdqwwrEKF6oDnYMWryuVDGDf1DTo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKo1xcy9Rd6LngbYxXMuHv6ih1EMCySGCk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKo3QBSNdc9gLmLoS9MDaSet1u79oegLyC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKohjmVefS4yxcwWu6i8qqk24KmRGL3gAE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKoNujeJQm4pyB82ofqyCRvT7fEBvazT6q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKoXC77UUr1811Sy8gTCvJoREUaWokvrjG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKoZtaGSAkvsCss5WcHyt1gxeGvmmVng9i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKPG7AHvwzSrZsPGxRYgyxNM5nP1GtFEu3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKpmtmuyyVZYaKtviQsTKeQw5oyoKDE5fk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKprFqGqSiVTfXanAMkHFdiYXsYJqpHHjL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKPY6ZG88cEXkrRU8J6rnaDARHZDAZbKmq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKq2xi5m8mtBg7mYtLgUqtKpzDmdDoFr2e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKQDXejoaQpFZMjqA8rWi5vRxM11GC6XFQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKQfcr54TnfiBJQVSzYtcidP3sV9g4uywB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKqpZEHp853YF5aGS8v6WdaTAnzwUXeekJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKqrPhLasqiy7FLMnkUWbJGdCyUvHf2qkm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKQrR789qa1yoVbkm4mBoMzwQ87pKYnE5m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKrKxcSmvmy7YFLyvYigWCyi7MixSpGN3R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKRNTxP5Z6S9v4ARwkEHAGtEh2iXURWCbB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKRtZxtVKsYfjXcdxP6D1ZCk9GYAfk3N6S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKrupX67vEk6oRyNhzZK1xvdPdEKqikFV4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKRxRoWypvEemXteJARP2hB7Y3Ht7fKAQE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKRy8oCchHykHJHA9wyJgtoty3hyHqCeqC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKs7VMYXghNXbJQ9QE3rw6jCUd8srGhGqg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKSDLYCFjXeiBXhUWGNho9Cjw2Dg4gnP9S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKSGPZP6djbXpmqiizv2LkAXgSNYJoY6ik") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKsJahKsuFf7fZjnyh9bW5xEmkq5P4iK5N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKSk7sFqzBT57nY6FFXnN8Ntzay9zqVPyw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKsWreVtCjH8A6Kh18YHABCze6aRjTmfiC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKSzDbjQ46MyyBETcABwqULhsqp8KsmayW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKTPc3194RRuWXibE5wWvQSXWSQLfR1V7t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKTuJbjygs9mC87kVFRiB5sV5bTXJjA1G1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKTxnGvnU1cC3uu9sL3ekNft1eM6DTbdqz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKUezKK4dKK4XgLWMvk4Sqs1mDaKvC3VkA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKUHiqDoXzsb61A2F7Qyfhc3RqKbSQuLiw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKuNnvJGEfn3JUzT1jqxMyZzDeFwkH8z1C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKUoPXWYVnAXgFFCeQmF5GmDea9dd95Her") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKuRMZgc9XrgTPbntHYBzyATVfwwXz8yeZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKvECfLA8V8CRNq8e8d4ppHRoa1tmS9LPx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKvGqpoaH92LStoWvYnjEQEPnUFvwK2iJK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKVihsgAn6mCFGGWA4RWr9QFULmmUEkTrj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKvL4B67yxq5aKbJnxJR5b9LFkEHcpa7DM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKvmYyykoNx3CSQ6RPiQHZEL9gXcg5zhSv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKVqSNPZcY3R3ic7iffbTpZcCG3wiNZRWX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKVW8eyk5oc1SLAxJ6EaYCLSiAj77hizeJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKVXz1riJ9Xq8fogZpfNKmx6RszBsozjuF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKW6U9nM2dRZH24WhmsX61Eo4oUyhEUPbV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwAGHVxZzfEGfjaUafXsc4jukZ8AuWvYg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwBLifP9hCSFwmBL2LBvbTNjXQi9vcJgm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKweYZNYddfiyjTcd1PgFedDgbPZTjiDcb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKWg6KXSTuyApudB4gpW1S5xvh4gJbGoNQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKWHTK9GWq2BaMfcjDpVoxGbrvNd5pvQTZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwjyTCZmfmYgZLdd999VuwCsNSf4o45RB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwoQizg4eTRBvMuBJmDYY7TCNJaSjxJHK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwqkd6s1jGk5a8ykY2eSGSgUSJ5tNeaCo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKWszbBbhtHrAPsVLYBU9At2n61ZhbFYKF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKWY1JvnRrCzpdyjTHWuJ6N4uKe69SabLZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKwZXBHGrS4Pv5AkxPP2C7YqfWLyEuTNzA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKX5sBgdv9K4mn1jBor6SzDj7irSuXYrYb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKxcD8ETi3ATa3Vxp1koFDoC5p2ttN9QND") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKXga41Xr9xEUS6BgZjW46d42a1yyGPqic") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKXP5dV6MewUpeaVjs8kmHFThT1wadLRcJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKXPCdwjZJWMt6ehpLma2nfX5oFVJBpMEQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKXUniyEKRcj3sjNeAU614h4uiVWnHLQiV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKxYMbE7nGJrNQSTpLZfmUFFyD7fVB5B8s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKxZpcC8JXTZ4HmvgZsF4xju1Te6j6pQxq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKYN4shbcA7r9HPAttKrpzaq7oSfJ6MNmL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKyRWnbSePv14f7zb3m21w7EiNWYAt3uhA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKyu17SjcztoYXEUMGysK7z929afyhSADX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKz19E6hF8fyiUiTtT6NiHu9k9y2abXPUq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKz4WGwL1a7DwwDoRGti1GXyAiJADqbNfs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzDDE3w752mBEjpCPZtaGu7tGYa3vVuwS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzhsy9t8uLJK9cfVNmDHQ12jAkWCu6GGC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzjagJfxwJPcG9fKSDidu3iXPdYpeuyKP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKznVWMRMfTTyxU3SjQYuHkRacGn32GcRU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzpuJ8QmypFFHsbxutC1rRtT9TR3BqvHK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKZQ3ko7fogGB8PfF8zQDQx2L1YYrY9tpo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKZSF8GtbTPJfKY7hKE83T1pNFYKsa38E2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzTFPLLxyMbsEsVbvX4gePm5v4CQxH2Mu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AKzWTtK4F6KrFaYudYjQpW1dP9zbuMwddj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL1vLV4zRRxHxfB2JnfS8oy3rdcNTwpnMx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL285C3uEp5GdW9jmZ92WuPeNTvE5FQrns") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL3KUmKLH4jPSrNpPfRBjLetomVxSTMLuY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL3sXRNV1vuBr8AjoJkaMDfNiTykKfz6Gt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL3wf6EeveE2cTFggs2gn2CVourYeQw5qs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL42B4dvBi4xDbbbyxEBeVomiBRBXWyXYi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL4AAHVWYNpuTygRzDbLPp2eTmeKcuKgi3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL4Q3FpEzMKZFk9gaTtK6dyWfGQyzMLR6m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5aoXuM2CPJE3hFMtEKECELbmDg3nF1ou") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5dYzWLccTCUB8GmLgbhKoFiiVp2Q55fs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5nyVzDWrfzPxHdeJmQUmF6BPb6jj8TuN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5SMsQE7FFKDz1PZsURrstzVrh3ErkdZk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5UqrfWXPtyKbzbYJ2cmnZxqt8vHmhDii") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5ybMUkdkKpUHAKBt2bJFNPwSrKHNRXRL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL5zQ8cSnESvvXV9XUVH8LYRedmX3bmGox") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL61zy4dDBLZ9R1Y2efEicSyL3Uea7HmNs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL66GG5xjKYArVE2aA2AEgoNrJziqYmNbG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL6WwJtuLbt9vP5z8FEPcBQYB1CCdE3Xe9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL7SELVG4B7NtFVvsDbQ5mX8piUpV8rMbp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL7VhWNVr8wnT1yk2onkRdvdLCUs4K4wCg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL8NxSyfbyGBMnSytx2bAFSD4GjJp6hiAN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AL9chnA13Qu61HSesj9BTDokZVztDVkXpX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALa5GHsmhHjUpMqftSua4xdAx9w9rqpNQ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALanXiNNT4My6BFQSw9NhvntfvwkAuUMpC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALAUUDmB85wXBK6sQvPMtpzp765HbKCtUQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALB573j2FwvPYBW6kFRUkKk5yAqnoYVDtC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALbBM6uv3xDBaxgcMLbVMJkgYtZnVbLBoJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALBMi5pfKXvT4wCS7Gw8y18Eqa8z4mfBsn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALBNozsAUfrLMRJnYrtFpkCtbfZWuzsL4c") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALbSKYukTNY4PqoDz3CouxkhgfXYa4JHdd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALbU6d847bRqpmnvrgxUL6UVLC6J1bNRT2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALbYWCppeUMnMkSHc9ygZw8RiBN3Nuhvsg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALcaexWgHGfi3Cv3eVHZEaWKP5yZLgv7e1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALCpVkSeiMRfsFKnudgKwEJZZ7ETmJjCUk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALCzkGfGY6dtezji2N5nAw4wmj8u5NzHAa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALD5zvB34ttgRBpmfA3nMth1pjFwLugSsy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALDkGzKKJVoGUWRLWndK212b4Tao9414oQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALdrhNtpgaARSMJ5FuKyEGKWuwyTcP5dqj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALDvdokR1SrM41UccPfxcC7SiPG9ZmGYZr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALE47gGnkLv1dZcEpQ8hWPpAoKmbZaLvFc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALEdLhfhBHZn2Jwt9MStv1Y8RwYPSQi6TU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALEgkQJ97C3rZg38sBdz78LWvyF43dJg6s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALEMko1FgGWp7daoWPW7qh8DsyFueFkm5p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALEqRK3Kj4fjxskvFbZCiWbbc1ChrxRJNA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALeRwiFtmboReBftiugVsnsYbCBYCcQjVi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALeS5xbX3jLi3QywJ2cKWMrGtnPdU8nCRF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALEVFbUVyNw5scYhSrPha9Hxdo9U1t19tJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALf3V1XC9f7Twm871KY4pzTr5E4jYDFA41") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALFARuyZRPgWXYJCKSoNKfqNbu76eyufsm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALfBSLLQXfq6m7N6rKEQHsVwfrpEUTket3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALfEz15zzLzNY6RfiCoJx4vS2SpukpCdqo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALfHWCXQ5hBiGfbXXkVXdeesjCar3Nesgo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALfUGX4wahRg7xU8b3txpZkbtnX2YssU5k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALFVdU1K8JzAcWSNNT7fFswSGwv5mHw8xu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALFXGbAa3bnfYjDY4ZakkJVS2Q9xcqDYxw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALGbT7UT4hssnhiPqZweoVXw4MAkTWEZJj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALGC8LwtX8pgpSK5MMghP9ESowMuNk1xXK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALGdVUj6BMeY9Fxzmoj6mc83nSdkbnVrMj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALgvExuqK1vKNEiWizhpFWtZmTCEA5BviX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALGVHqJj2ntRScujrtsup3rpSAfv6bwAX5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALHbRhSqLkyZ4Xa9KXfzmPgBzhvNn1P7R8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALHnYidaVqp5cvR8d3KKmduSkzapT5WNUc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALHPRGs5u99gfUYtSSfQpfSzziPAucmu6U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALHUMwQD3LMRVPn25mpKst8qQ5NtfnYqDv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALi1umgaqVRvoCifik2vi4y86ghRkiDsVb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALi8MbdG8zzpQavvV4SJWYHq9qxUCvcCV4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALiRAwcUi1abKsWwfdgqYscZ9wSsC4bJJJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALiu67WTMs4DQoHu7ZZ8dDKN5CrhhSa3wr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALjA57ZyReAmnUEpkrxW7a9vktC4NwTBZV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALJAjfV3zBz4Nsr1KJJtegsP9MpD3p9z6J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALJeDycypqd978dH5mu1oBWvkxT33ne79X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALJtAVr6neXdswWBwuKz7QiyisBGC1ARn8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALK3uptmDnj5jZ1xZMzKj2a3KCKpzG4Jy4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALk8dWu4Gm557xwzCqgMoaycuSc4fSzP3a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALKiSQ2Z7BzGdZAtx2TYY9iEKKp75fW5rx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALkja9gngrNs2obk3bEju5a76nAxA1Q9XV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALKmJHnDpNrKnv7z1YFm5YM3HCMER6saF3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALkn6P535vHprZX3TRTHxGUdhPUdFQb4fv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALKqHcqD7jZ59fec2pX5uJkc63gbu6WAgf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALKuw8UApj8uFhZfugFwcih9AYLN7FUeAi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALkxAMFGgU67SEahbT8Ds1eHTFeKWe7i6W") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALkzAwZUvX8jwtzGkEq4LRGdQUHbDLM4db") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALMD5MHVMcV2pD8kn1puA88BX8o1C8snsf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALmGbLGiwXayS4afC9XketJVqcJ2Emdk1z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALmjkPqpuuCGGVc9TcLzwfjGXpGMeVie2h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALMm9kKCgz28AeWrkiJ1gBjwhxsVy91chi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALmpLzA7Qnx4xfrUzSgG1PoFVXEnPgrRcD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALMRibrCaNwRteUhG94roJPqRfvEWoJuBG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALN9c9wd4Cv8ucnarwK6vSDr8t9YHGaiVs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALnDQstmQc8rF8EhgxmEmrc9yuC4mHFW8S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALnkhs2o6RqY3XyD75Z3RfNaexjnsR1zyk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALnQTCx6kH2PJjSTi45jK33V4k9Tvb4iUT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALNrEnz5o5Vh3ewK3ZNAZFosHLVENrTceY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALnSVMifm5ZtdzxXdNhpkqrKkzkvZ5C8Rg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALo8RSEfzMciiX9cdBerLXyF22wNsJxtao") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALoFdZShn84vwusprGhJx4Mw6spmU8Mi6Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALopqb9HBmQmv6b3vQxUdByjNV2FhhhqS5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALp6yNAF3wu6ZzbEY9qfUJL77uc8ujgGr4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALPTrhkfPUDFsJBmxHdnuirDkecYB7Hdxa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALpzBSgDFKDnhX622VbiZaSP7GkjpsymyK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALQdMrXrJX4ycoob7vxYkQBkv6DrXDkpCn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALqgMRJDBnbSkai7bcfW6bxBTjYcA4HTpC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALQJFecK6mDpYAvE3P7eCenDdtwNnb5eGm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALQjqMbaLDSBYKY7oYC9JQ5jprSirXrpgH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALQkn7gu3TMZC49az9BBToK62DKTyjdcvK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALqRCWKiJ2Uo5mNXUKThSwRattjqfkc89E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALr5KbquTgKBZnc6pXLaXcxeitFZcTBTbS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALr7Ypj2TzTRaJiNtDhNvBCUTg5VFHy4v1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALRfhdRmYeHmxcrXFbsPYkctKbbEpRHhvy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALrhgf7UpaRWiLYsLCrZYUuBYRC4wqN6ov") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALrjeZpbWF1NCgCKMa8FHh6TV6k9GsyJmx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALrmajDxDdvyRNA7Ru6W9nEic2f836RskB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALrmidTWZgE6K7ur6tNpsiAUvQT1rn11WF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALRWE76hmLo15UuckKUCuBz7Kw5LGpq8P6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALRwnKS8aAbHebUJc4kigg3HFfuiADGhZK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALrxfpafgUZ8cAZbMoBSWXs57hsJPWRRt7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALs718WFtva9ifvgmCDrqztg7DpmTEp8YE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALsAtKwxHwFkarR6nUXbU43LDxkGYk9UWx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALSCMQ5HTF8qJczX2eZRSkVfGoFuHjwjm2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALsG6hUKaAQfmXPLBxoDdRbJMdFd8vuYRi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALsHqd2Th1w4djAGP3ZCos8BuZ8pVw3H6Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALsHRV9b9BDhiKKjMEpgFEpp1XuVjsL91Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALSJSt4kAhNoQKKVtsCZZdDRQb4kEuasVd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALSrYFZ3aPr8gqHzP3xtKgevz32BtWsZQb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALSS32CEbytDniModfX8JTu2TCoMkbhdoB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALst4R8FnJdGhebDAa5wGBkaGic7CP7LsZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALSzGshJtKSZ9Z8CqthV9Jm11c5Xir9iRo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALszn7ksRj1RgdtGexMZ6jz9YHHggcnMEV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALTagR5v5MMmyRoFAEzNhsZBcQnQNjC2zd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALTcu3zDsEXjMMgUwZycaoVRQRyXfpMtsW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALtDydbmbiVxdtFXgKxMrp2jxLx3xQJyHU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALTEwzv5hWjRfgh8uXzs1KizL72QQfHow7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALtfNq6SVb9U3BjrSfkrQnHVfWgVofuhqQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALTHMFahstf1sFuhnN9HrMSWTGdfrxgrFd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALTqTCYtZnYvVvzJE3Py3KGuxdrp8WPTKR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALtvBn6GDAU3SMivqj5pBhwQYCypykeUDH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALU3xvaNJxUX81chFvRKpaL2ysjjmsejw5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALU7hs79AxvRzxpNmFQ2Q55J9LM8JbfMbC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALuaUfPq7n1FSdbwPTvXGoQAtAj7v4eEf1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALuAWRWYWRTVruzTLRFXR84CtKKxsEUSAK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALUdbRDtK9NQkJAoA25poQfy1PtWYWG3km") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALUFASg8ZDvxuMPCMJHMd4tyTmvTNdvDtj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALuTsyZWaGXZUJbxnLnGrKaEx4nwAJM1yn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALv7WXc1D1cHADADVo74BqfN1H1UvuDPgj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALviUto3qSKQaacAQh4M9uKuDYSYm4RBzU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALvjX342BsW3AYkfR77rdK9cBU5boqtmrR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALvprYadEjpVbNT8yqykRMqCyeGCo96nnp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALwAKgGzqt3FpJPPmW1LDi6R9EtFAEetQr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALwHrJmbrsbGfrLCwF6qhMonT3YP6n2MXZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALWiNa1AhwQCRdiKVBrgKoaDCw3X2qZ883") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALwjbqKJX89YmMBfUEnCr5n7qYYvBjFQnV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALwJgUaonWDUoJf9Xos4JJN55sRs5iLVHn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALWVwyYB28spNYecyXjD1QcfPjB1vzw9Y6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALx2bmD5wmMo8kb6fn6AEAXEC715wnc6kq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALx8AMQm38qU2B2UifxBL8Ae6LtZnzsK7Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALXdDahDBZu8J6NebiJC2aRehwtuY7ysCq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALxqdBjDMp673X5dffDBgob5GRECkarqt7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALXXQPPRBTjWBZZHKPsMRxUSUFUpDppuET") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALy2tmfbvf3uWFAGKxhndsoc2j9thivi2v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALY76J129FsSr1mjne4BopeF7foos1be7e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALym4vN4u1YsPbFDp9iwEoRS2cH44MY6hH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALYofGRvjjBdBi9asVLormYQv9LtuDGWpn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALyU2zK9FAw4C2mjZxGABWZiPCpGfeBEVd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALZfBpGgHoBGScToHLiVRfLFs9iRwJrL2j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALzfS2YKHybC27PQQVwqZsuhkcC9vPspUz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALzJNFbfmxEEeoHwH3eDq3BkrPsdLHWk5w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ALZQ3pnQoXAHbzDTx9C9CYSk9Wx2M4e6hr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM1CcngjSyM4bvV6D7enUmeFabpxobgTz6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM1mbLJWtN4uSMmPQPiQ6X5WYxbgKmTh4k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM1q89WapKng11PzsxdASKhETbp1MrFMPA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM1s8cNqQV7s1c5SNgzsitYECJRc6aw43a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM23sc2bbSybMRrnCM1EvbviSrijSRBzcp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM2fJkgGyzm8K89sMYhDf5zgiXzYtNDv4v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM2osMjMrxCQjHRhZtRAK2SSRSQuL367qJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM2zZrAkY9gN5Nz1SMShKdbQWDid7vRr9t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM3PMssf2X25yK6dNcDHu5joNDyTR6euth") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM42mDVGRfWYi7oX1hGEWnNWXhXmpfTuBV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM43uSthBkJQovveN6rP74eRCv6knbCbfQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM498LyZVFfMo3JaSWGvM5JR5FZevXKGoL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM4geoWu5HihNxQ5Jauqz1Nf46utipsfTj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM5CdzgHj1RFAyuymz1XdySgmXNCQToySS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM5ftD6tKVrMPRz5ZEJJSCbuSGx4osWSes") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM5gcQtWpxNADcNCzEouNuk8LsGepwnRNC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM5nKPQRFC94Khr5P5sFfTbWREuuqNFLdG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM5wsMYk7jn2beZSc1VmTDHrdDPPd2JG7w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM6k1EksQWn8QxvMakQs3pUk5eGXEMjbg2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM6S9iiKRe9dMvD1GLWYDLXfgUmvy73hVz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM6v4BuhsKp6vHbnc8wsPFXKJP67AFLt1s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM7N4GYZJdF438xWMxF98Jztt9rLkEodrM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM7ZhyjoVMHNzcFATXA1V5PSGMRabgnY7F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM8TfcTxFFRAFBauYBNZtbCBY5bzhKxoPe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM8wogCr8i7gmiEHxW1jKYXtki8gNFPZBb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM8Z9t9zLvPy5ii5QgWetNnnL5oeLGmJAi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AM9pSChvtNHRqL7ZFCiLDZZFLbvNBagSNA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMa2xibZzXEXsHs12xxuKaHxdxG1QuUt6b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMAaaoyNDqwiwU4U5PtmFx5BgWUyD1fJaS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMAooZFPCQyFcGpDNwrfVuxVtBtRmC3ow5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMb77MfZxpuWtfAPjSvkfyQiRjGEPz8Nwe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMbGKK9zA4747fRQuKsJPu7eHoGh68gB1T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMboqmhc8xKgrxdPEq65BoYxB53n4rx4pR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMc7DPComCbA6q7DRE3hbVFTWQnoHFvPAh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMcbUeV4uTQgpLkfkePT2CjWBKDpJA6pW2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMcRVq6ade9jL3FPBnJM3Jj26bK4BUHNLD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMcZ4DFEb2ijNHaAV9RcSz6jWhsgo29aJP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMd6doUSh64BEWTDVFu8dMB8xJLcocdbqF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMDHwt1oQQVrghy9qb5EnULNug5dKH5LnR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMe5PCS36N9guq1U13J9Y9VtVxewtjJTwb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMEkktBx8VMLgF7HZGCBqaSSnK7PV2j2kN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMEkytHqwPF4SLxrefi57teVrmEmxGNZ1f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMELZ17eQ4CMzdLAe3fib5wTDCvG1c7QQk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMeMwjiVKTmH6sWAcBfYSjJ7nfKM3yNUD2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMeZg4rsmqT7M9Hzf8PRTWyAuBFpaooTW3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMFbKZVio92oRu8C6zPye8f9thFcuyjxys") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMfhNAuJYFBChBk6F2SbjBTWpSFAzx4Y8V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMFqPQhrGWGpV4cMGD8Ui11DEPdZzCp2Sn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMGdtRRSm1fngmJrqmQRSEm6Fk9kirgkUq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMgNMcikSAacHN4pkthqRnLSMjJfwV3c7d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMGQQGpyUrQde7bqGrfz5wLPscUJQ7arvR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMhdsE3gTLN9jdTY9ikNxqriDYNbG78P3j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMhnLLVhkGUxFBy1J4cntsoyWxQsAFcuoq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMHum13CHPaGEHczfV76Y1qbqC5Eys4mna") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMhuunvDhsvzosHFywnHuzrHiS1Cnu1xhY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMHwqYbM4CVuxAQ7cdZ6oSMjHpdaChQsf2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMigesggpWgRjYBzb55g5yptX9bzYWc4Hx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMiNWge3gCmxjGZnA2TdhLLgLdxreq1YnY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMJdKTBimGA9jL5rVXwvmYuGah72ZkHkRH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMJE7XSEGxh5L8oZDKeUF5Mt8VWiKtMFzf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMJfDCfyiRrsymqGPgZGzcK2jBoSfCEKC4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMJgE7PE4XXG7UJvhnaBeTg7PeeUvnAoq3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMjTtXhWDc1PM1jLutiw3SyGWEa58npLos") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMjYTCqCwMfByH6XZ6FoEi1GHHkTqUm3s8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMK91GVDYESQNNH7L3JjJ1GoaAoCNuRV6R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMKhiFwecqrUdxKrPGU5REsnBXZKYCLgZD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMKhpL8hU5nqdL79SFDTiSELSSJzVcCiCM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMkmppkBcCyVTfDTg8Y35o5dpQ1LHs8pdw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMkPBGBJvoAmcFvhCAtUYd25XxJXSYJRjB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMKutECDSXVK8oJFQptbnZsoQLnEyZEbus") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AML8ySZss7igpjh7CKqzni6ZUgEnswuKDC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMLcUzkvEMpr9E7UAiQifBs7M4w62vM4Qi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMLs7NzPPrcLvDW95zseAXLNkLhmFrBxSm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMLz3e17jRm44bGYtpr8NgbdyWSLygZ5L2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMmCT5wx2DugpSSsdtfSmwKTo4zX8B9eyy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMMfhfegNgzvg5qBn22xquwad5Ah6hHK6w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMMfiJnv2L4FY3H4ASKeA2cuGoKm9zLEoE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMMmApZh3wMu7kogDnmBubZ1ZS85sLC4P2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMMNT5hY2LTkYCwaFeYWrSoYFKhXp3G8Sf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMmosUKqfMYJwwQ5MfFiXjBF1kPNxPRvGd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMmqkzQyZNnUamdgTVkoNCbAPHyKip5oyX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMn1drrjAdLQbGHrGkEZ4SnTkFYroLwdhQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMn2sZqNGxEw9eGhsUhWRB51XGxjuXUNG5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMN5MBgyafCjS9AvMFeJ5yCrhgjB511MfL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMnbeZ6teuxNDphw1PCtAfFF6LoxTv1oGd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMNiiLwp7PWDbxHtVgmHME8ZuFdGS9vd9k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMnP8mW4bdhi2B6B1A2idbgZW4nPAdJ5s8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMnxE6qnYB5PWXhLgu6eV6egf1VCgcXrj9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMoVYpdd3nic3WoELsnVHqExPBfkKEeRcP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMP8wbwsypHXS52f9kcAfhVYVogJWzFU5x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMPbcsqHcEdH2L3dUMg3xbnoQEnar44SkV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMpCf8wQPD2vxZRzCiBdu8yJu4L4FQGbST") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMpe9NHutxa2YRWEfWxhKcMAmQhEs7kKsA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMPffqwyz4oGbndfaBo3wDnkbZF1mP9VuV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMpifyrrp1UP9v2g6unjmcWXKZ6xQh4qYV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMPqY96LGq42ad2HvfiJnKNpLY1HeeFJYf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMprZNoyVLqeAv9HpNgpFpS51xn8i981M6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMPTXxGLYnmwF4TiKqJTjiVRN1J9UBqcrW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMq8mK3Eg22FPuWJYf6tkPYdfPnP93yTDn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMQngdDyz1HM25Smg2rFrJhY23WUPxoTci") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMqwvDbK95Dyhvf7uvCcxJQdyWsYLAcaST") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMqykXvYjBsgjoMpTYAhGzZ9ks2otciCYY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMRbwWGAeB7jTXWZkPZRwoUZjijiig3DMc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMRFHtiiSefvPQAiWvpZLxqSwtwZkahn1n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMRMu55qCT4AaLvnJ3zZ2UkorRfpWBCgQ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMrsTM3KPrG3dmTuzKxqTZaYrhC1AGWk5z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMrTPP6uWuW9mwwd6LTqQTaZNqQGQVbBYo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMRVxScXVcCZb3E1uUPU1STKFwxrT9YXu7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMRxSSGg1P1MXacfbChNFAwSFPgnEGhQSN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMSCoLGkfJHiFjtXci7iVSx27QpCzXfj62") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMSo2MFTeEpQDefWHUTSm3KQu6gvdBbqcc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMSR27X4i4DPgubi1XxWEvXZpahJnjV29d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMsSoZocM7z3jjUHftXAk9XFna9E1oiEna") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMsu6J6gMZ1Q18aFhcprao4PJ9JJ7dDfvk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMsyXkeN8UJv8EfSoGUgs1XUx4597ZNXLc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMtksKPqpGyBcrffUUNCESKEBWwkKM44GN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMtmWLo1wMkbDZWUf9UFV4fBWUJC9XnVsm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMTwMsKWpAnyVCYTxQmY4oTpjD1G2NYTGY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMTYUF1Gv7hTtLSTjNeBMmaegZLdXmVtbB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMTzBr9Ky5zePzrRUuzoYfNewwGrewYGep") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMu9r6cgMDApZjyYuwiMpN7SA5N8jBNnQ8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMu9XADnk9Pb9bYQtLNRvwYkviPkkcCn6b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMUe5QxouKLT2BYarawmA1bzsaQ5xWBrw8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMUi4By63kWzWx1XMQbWt2EquACQf3cbRF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMuoiwC5kizU25RPx8zY4AZBkiQwrMaV8N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMV8cccMjzyTEFAWoRHys6jCzbg8bVNoyu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMV9q54ffTR4oW8EN4J57XWsGX3wpf67eg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMvjZ5KiyUXadnsPv251XSpJ3DQQj35WrP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMvwUKkZug6HotZutx9GDSCaHYxy4NpThY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMW4RdjJAswpmN6EWRkWoB9JXDpZ6We9Q1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMw8LhKiNX7WDF7hxkXRRf3Qi4moCb4HhC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMwCZjXTLm5gNYirhRqLojeSmyG1W6Sv3G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMwkWVKWxF22rcWTFHfELm5yAnKrRKvJWN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWM2PdjVrkZEkXQPwvR8rRB1YBLKNtis9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWRMBzRpyhNZQvCsbDJJ61UwCwiSw8vgX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWUigdtXCvgMVPyuhNoV8D7eQhZTiAg1E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMwv9Mz1Mh6Az4yRGYyCSm9quCbfQ45FoB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWxg1sB5w4bQJQppiLdtqYXmaDSBpypqM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWXN4mz5YvWpKdDWvoocaoiH5yKKsiysb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMWyd6vyA4f5vZVva2HHQbK4S2wdxVMuun") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMxmjErxufbbdKjnfjJrojhpaeVjUR6S9G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMXsoyV5Bwkwy2j94fBsmyvJSrZKvceuyg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMXvFpYsBxuDGpSFgcJCzxcFuUBuraxNvi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMy9yJyC7EuPfeR6LjzRFdgmeKMSLmV3ze") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYbEAVXtZ17ksMyxsaBjfJTgsXdH2g3r4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMybWooET5Kv71MuiAB9wFmDVFdjEDW55i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYDPweRLSRhwbBgnxWbJ5aoKoFC5Kkaz2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYhKAVUNxnxQ64NqUKU4bpS9pxyU8UJeV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYtMqX3Nz1QkigmFRUm5HZ8ciUTGyh7iz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYwriwHp9BFCJuGDCrNwYBA2JbRrXNCeV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMyxyPEqNapwV4Q91XP8n7egYsijueZmcV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMYyKVFDa5Kz9AQ8bVT4ZyfeGVRwT5HDPG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMz3RoiGivKqq2s4KF5hBttnQTR3cyJ8eR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMZ6ap8mqDbWniNAfSeWEwnZu7r2hnw6m6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzBuQKuaVX3smPYLfWRu3gXX6mzRoqV41") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzCnmy4qgDfmcM2zCxQ4SHcxarN4hcu4S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMZcp8nH69h21St7pXaKVtPvcape6pc5ZD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMZE7zNME2HmV2HZxoeMSDfnCXeXqKTNtR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzMAUZkC1buoUUwGmutcxgPvzcWsQhRQP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMZNfaRnr3s5E48wtHFC5ZpEJ9FMajVsHA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzp7mQc3TSNroVga6ej26LmkoS6bdS85x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzq5A66jU9ZpxTAH55wfqdvxMUaspwk8e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzvqXNUKCwoD7aY9RGYWXkuMDSxYknkwu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AMzZyFDE2SRpiXaund4ibJZBryhZMZAdZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN14N1SipUMgxVJyYif57VAuce8yTk7Jxy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN1FpXcRAUBpAMgzmGLSTzcCWqkWeR4xuh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN2G1dEUv13WxmnDWW94nsEfgMmhjatuAP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN2VUBDYuNru6b3giKa66p9kEebaF5PnCV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN34WVeLdij87FXaFLU1oL9fkK3GfMAQFU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN35tn5L8pXb86DnBxWe6vQkTMnEiM3Rbk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN41p3rz6rdx9qDjbgvYAdufFwXyoHUpFK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN4R56i4naZHY3oNrGrbJGSrpC62CFRNqK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN56LG3sPMVK8deAo184SrRMq8RKRayRfn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN5ufEKAjSx4DRpV6suWR8YQS9ZekU7gan") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN5vg64xpshDjiwa1aJwNPzCFR17KtGEhQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN5vY5uWSudvpT8yDpSxxm7GewFK1gXKQB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN6bvgTS92KPu8xhdEkkCutzGe5PqZxQEJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN73K1JV7tcNummcya9TYWWzTkL6PCrQHv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN77uNVBvBxnpGQp3kWXP2XFBqfj6bCEVN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN88EtJCq7zbyNz9ifbLRWyUnGcb992YTY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN8gzBWbGbu7jVgQuW8jhq2xwWEgc8DTbB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN9Ax7UPh9DnnH4ffTQcMq6CgVTrYjfaMT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN9g5RR6bHZDgDQEHFc3sG6BucYUXgWGrf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AN9NPczXJmiB91YtsupSswmnt8RjEBkUcq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANAHpEeRQD2RqhTkMPTi6SebZeMwnyLy5i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANakyPu1nTHE3XYSXQKwFsR2pVyDZctkiB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANan54bohWz4obpz5qzJwWXxUiPhHdHrLP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANanTkhbTLfYhn7quise9JkHKXmpD2HnNT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANao9kgAx4f1ZfbJ814kt6RYtp3dthY5Gg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANaSZ9x9fRVx8p32ACa8CwWEWce6CiGSRE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANAuebkCj3zjvCQw94RRay9CznbuL5tSgr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANbGyQo9siR135bUZiAbzP9uFsCYvUSAog") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANbv7dYTJW85EgdeAVHT5H5mxs9WWyYsXx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANbxDfjfZEvGUfmjRMi5kKGHdAYuWi3s88") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANbXDSJHhud7wptvFRF9a2vvm9Bzc2W3uT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANC3xyS1zPcBFuDyRZVhmjPmUGVN3VbrKZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANC9RKPhRi3QYkE51pbRD165Zq9oCZjaws") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANcDAU2mpA5uYppZuDYnU4yZiATauZdAzR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANcmLfeDjoBc5ZUBLNQSN7sWguKCwYmDKX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANcRdistzLY2LMDrFYvXsLzR4nef6C6HsN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANCUZSSS5KPTtpPrUJ68NDX51YUD6mQ8Cq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANCYVzQAXfJzf2FBB4Ngb7VRNfXAPCP17P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANDAXJrwP3fq1HkvLx8tkbTRZMmFX83vTx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANdevAoRFicPPL65mWG5fyU8dkDim74NGk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANdVJAQUmQzQaU5KnGUmX1FsB87XbHAUau") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANe34AZUDtk14qHq4Jq6LE6CPw7rLT5YHE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANE4x1zT5KVfbgpuioT56oTkt4WJ8bJkWM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANEe55MscasjzPAQNWgQ2jBgrgTT7HdFHB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANEEvzvC8vtuhDkZPKsxs9gzhQvtVphpGK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANEitRfgxaTxGXXbFBUUMxkgyV68xqLwpx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANepr4F4TsSDRng9mv6jBjcfCx54vQ5YQs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANeRhhWdSZkFRT8pmQ5mYrD9mMtEtypHN7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANesvSDq9LrsqEr3mGoMdJLPsD68RmXHFB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANFNiXZ1eYEw2kmDXgezQzSmDfE9W6y2v2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANfPLHvQWgKAEvUgJc7fsEr3fYMnydWbi2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANFuaCb1dnfNCSgae8TcP4nhGFB8ZtUBKP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANFuSUBUDPckQpzujmqRqrcnVbUujv24UD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANFxM23Navv1j7fqpaJcAR5Rt7ua9hrnzA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANFzFqxmWKDHo81eEYfrvnhfQ8tTGEWssq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANg1bYGtntSxAec5x9yTtq9rzfTWLxQBDv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANGkMBEDfpuojSBmeANurfr2HWnkCgghE1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANgL8gw1bBfyGTxoS8HUQzLnmqWovLeKku") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANgmHsn4ENLqFxQx2ztmGMkwTTajMbSZmX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANGnkqAVCGEm5pvbDv5Pe3Vh6sD57xjcbi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANGtWHuyfiix5ae9gVmdkmG86hUEUTbwkY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANGZy7rDPVd9pirmnNsVoqGSFT4hpCFupb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANhdaMxhaxaLfbuLdnHTCYb58g4uXqDAxs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANhEggtg6jfwmTC4NjFvJqc99nnP6JUZbw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANheRJVnE6hnj5gAmongqQYiTp24jpcscT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANHFJgLsi6P4Ssm6JvTSd8gUFUvW8o5hyE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANhggDjdBFPR9yTnLdZgJoGWMgy4WFpdN3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANHoQaP2bjzwmHb8jN3Rp5thG4hQVCWFta") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANHpobP3aRJXhJ7yMDxqWF7Fzj9C7e4Nad") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANhSEhXAJrBmDeVeFuRtDwE1XfJbhXNFg3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANiHVXxdSnJftVoqPmuXz65MGVSdgyKs1B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANiMyc8Pdz7D6pCx6vaTVt9QbWZTEaJ3Mk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANj8TPFinm8RFTffUZz1DTjRMJ8jav3oW6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANJFqxQ83ispTnFQ7MmGaXGEceCevnVH1x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANjG7znUa4kbGvh7th7kwrsvF48tGYoXvy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANjUsTb1BRdKMvBg5qLHzyK4nbjrT8jEXs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANjUZYMgigtRDpTwSHmXvdFAGaM4oYeph1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANJzgSvm2FNY8ajjeW4sRD3rmZMfFBW5oM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANK4qEMwsHvJ5WRbhw2X9uBqrxU9E11RSA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANKMUpAZge8EmyjMJGeFgeBP6JNXpacZ4W") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANKQpvimZ46VWjCLbQwGKxh9VSQXqytGmS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANKSb9e4fGGLbttGAxa7UGAc7awTivCbGk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANkWAtw3u6HZCQmUXekPZLXxwG63Lc2iw7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANL3jRsczx32fYMA6eFqhkw4F51N6rbriQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANL9Pwz4hkmUyJJES1QyCkZT2vk5DRJYA4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANLCXuyqC4aUvaRk6RAe34tWQ9zzBsptEE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANLe1U6N8yBCAEfkigzDUfub3DNtq41dhj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANM5qo2Nb4sBknBYEs28JZyc1XsqfNNxtR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANm8xqJcPepSuN5yGiNd9rrHyARFWTjhFZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANM8xSPi4Hndi6e7HpxbjYfCStbReu7SX4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANM91MFBT2onoz1RJAgGHkUQ7EtyZmhy4x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANMevQSapD7EDQGNULUE3KnpED5guGbgWh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANMJeVoH4kvrLpwNKZkm4fRZNtNTyDhejd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANmqFrrFZFMLsURwRXwCnxeQYvbam8tBmL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANMRDP7niamoLjAVWhssMWzFLtHVoHynpR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANmu19gqtTEpsA19VT2nENaryy56cushrB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANmvcrcrPfo8jSoBBqvK4D8BkMYwhkrdB5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANMxm5hGSyCZN2k2sG5fs75pFggbuKEzny") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANn7J6K7PMajyt9cEAixkHwq4qr21cWyGL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANnwU4Spgv57VAVpiBzpEHJJCAARBjSvko") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANoqKXSeJcuHcuHW961v2XU2xSt15E7JQL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANpah5jPNpG4YFk4CRgaq4p96io9Fu93x2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANPBuhfqRDrEP4VeCdMTawVThmBpLrEdMH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANpXFb1sVeTNjKfK42Mys3hEaTshVeWgjH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANQdsaCUyy4NLJAtyrLUwcz29vXQggYLQH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANQEJLp5tqr7V5ygcgHJkAaDB2m3AsJpnF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANQFpupJW7MDFMP9k6am8vBJxWQJDndmFe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANqvCq5HcDBiuGXujUM2d3GBqPYDnQsuQV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANqvk9Z6q8okzBo93TkPyweQJvpRycJiKr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANR5EjM9nXq2DXc6WaXNEN2GRAzwCufn7t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANrknTfYK16NMo7ZNBm44iqKDEwoUoG1Fh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANrpk2ETt2fL5iqt6gn1U5Wk6dBiPHnQFD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANrpkxaDzMiSnZp2rSmtuV9jJs2NsZ3m1t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANSbZJBgrikCrYy6PSNAVV4tGgwFVG1zYn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANsnQsrS13eN13nGGTmkdqmPocwajG3yBr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANSPeGf6dUJZw6YxXkDEhudcoh4nc5Vhzo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANtfBMLXQZGqwBHHAWsP5cozqy7UZp56Y1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANtHp49LP6EABcDN9kvzKpjosPdkG2FYJj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANtjyqihhybfBeUvuFQ1BtjQbbKQH3WcCc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANTPJkj6Aa1dX4pkNpbbNjU6xJcmqTjnYa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANtZ227r2YssMxgqLN8B1vppgxVxhc6ECi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANtZ8Pqy4Usa1bnf4njXaRPp5ej4XMWGMH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANUBMzdukQCAX7sVJfDfyLs2cHc617TiQu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANUhwfk22Z8cScsM29xtZZiqokAdZ1HF8j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANuMLpf4GZuDEypKAeJN7DbQWWvQz6ewEb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANUNtY7eA5apsC6CdZZehzYnyKdefC1DLi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANuPZZA64D3gbuf66KxvYGXfd95BX6Ffzy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANUX4KUEYh2qH9GK7g6n2r2DxcFYK16Grf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANuZChWWAWKbZ4ket7ME7QJEBebrCCUF2N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANv9qq27isya9Eoo6aUrr25YRA1XUJdgQ8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVA1xKLAGDnVQKNNNGnyy4K8dqy8TJzDb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVAyZdFyFbG7kzSoXDrHWsZFc86k2tFbz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVBk4MzhkaHSAz9u6urxUFDpFjCbSK88v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVdbipA3wjhjVRHGof6227LrdFXjhzRCT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANvMwxNPADYrJ69tBdhhqQC8WrHX5REiyk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANvqiYQnaRm57WHBy5rLNA1gmDaf8TwuF5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVRGhU3uAJWfVDs5NyxdWxY3ruZnD5q9t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANvtBVGioo8Kow4nfnwSgpV1qkKroZSUYS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANvtK9dtENwJLWuQB45amddtrYncBpFbbg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVYFkUEyfVQyCuwrENFYwvv4xobujs1qi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANVyYgN9TFfAivMwXLjPL54oUBageHAiXn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANW9g73eemaMXXorsjBkUTPZtJE4YizupT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANwfHzWuY6KW9eyPC66o3GiesxevD7SB3T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANWQJUX66nb33LofGKzEAQ74krjP4xKNcK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANwRGTrY1ebo5pbz6GKoAqW8GyMkDy3tyA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANwWQ6CCGDL7whXLCoeiwDycKQC2Tmf4aw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANxvEzbKsEo1UA5nWafs7yKWbeEuDRHLTM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANXWberAit9Xcp5yYqCgb642dmgMySBp1m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANxyLLGpRN4U6uMC8S7z48mV5n5m8jLiSW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANy2iqqRsWuoS7DcySxzUF8h9e8Wjod4tY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANy9r74273YgPza9fay1pFFQgVRnhq6PkP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANyC2LCWk1CNYRkBgNFX2hejYJn1ywijES") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANyFgMguqyFMbqWj3Gih8XdLsfTwhMGP1e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANYGSZH6WMBgpBf2NkWMhH9wqMRvoqmEhH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANyJt7mNDfeNifa6woXguk8oxxX8ydo4v5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANyq3hgxrhnUgXFRkioXuHpMDzaU2qhugg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANyQ8XG9BdfbHJfRLuSZys8Fr6vqTyDD6L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANZqNVDCwF2Wy1D1qmkgeQHKL97QMzpUXv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANzqwqvu7LXAHGCFweLrFxqqYFNA6FMbpa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANZTQGNPctw4vazQHpXrUmBiDmJYdxEGfg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP11QBfZ4hUrTHURvyTCXNtehqimGjrTyY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP12RVwQmJ1SUNyUvttBdrkdbzyFTCpNbw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP26h9bkkckkmC8fac8ooRgmBEHdmf69nh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP29ZvBZPpvASzPkKq5EzaMRP33PSXb2AN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2ceLEb9gANBoHFWzKsskbtiLEecxC9jN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2cuuBqadV69A96Xo31ktn3mqZjm6pizt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2PzqEUuyhtsCdpAQERiWs26AAExDc97v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2TCmERybjvr6RiN4Ygfc3NXn66Rz4E2S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2TFhgqh7WfN4Du8hNFPrSi9PKirHQRPy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP2vtTg7JTvgfZvm15GYKGuthXHZWtZT4H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP39Z3yTtbT2EVMfGQKps9Es9un6x6T6Gd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP3QUGTLEVAVtfqbKq4WTaFhiLwtDiaGXi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP4AG5hiDLxt2sFSwy2X2K2LBavdj3fPrj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP4ds7FHHWJLQpZbYydZa9keYnZaP8UtpH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP4fk3VRAmSGX75XRpW2hmaN3nVLo9f3kZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP4S4tr2x6rAqxEmGcTqtC1KqjnzQM8589") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP4wi1X5HnpqBrAfK9wu2N9Vvb5xuwDApe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP5HL4jJ52ZFop8kezN1VJBT7xjKWVg791") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP5tdEdJtZBN6edo3hTKN5HWE1QVjbHwWn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP5wSyyR91gWdpxTW8mG22hxStDJhCNYL3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP6AMd5Gh7DZJsuGGCBiPpQhF4KPVbJhbP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP6MZ6cKognPQzw69BmZ6eo9kUBszcUUFf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP6quCLz1xaeYeH1puYPuBVi6Xh2i4DcLR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP7BFjVgSLQ9mLvAe91E5PrG9th5QAPj34") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP7gAcs6A2sSiF5dCbJKsJApBt38GMYkEW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP7ooPyBs7y89jTuXzeemBDjmvpxg6v6iw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP7QE9DGRks1nMWWevZLSb7Nj4sFQi4H2v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP898TPj1jS3SPCnYL2LagmuBwpdJLWfRJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP9b5c3kN61Sy2efvXVwE4VDLXotqz9cgC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP9DDgaubP6yoPXGr1yjzB3b8qcsh3np4N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP9oniCSxMDwEb8jyBa3QiJUPMQYDcTRiF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP9sYMBkLMQ2VdFCUJuq3J8jntS1UpyPaV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AP9V1ine476XTmKt6wLfeyxfCwhh9g88v2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APaAEYAtMrmgSHUAg7p2RE2eHRopM1u6fJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APAEAnfNZK42DFpK7iVGjGq88qFrGoSqyQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APafLhv21sLnmZyfR2eZ2CLZKKYwr7XbJe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APAJ8TwU1dvyW9uvZ3xzxYe9CPhK6UEf3Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APAPv7sH5YD6LpJtwh5fuWhonwcCKbvmtD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APat8ccBaVEYL8JBeM3PAX7jAhVjrNXU8X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APb12AQeJGnCZb3NVoyUirodKSu4MeyNoF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APBBjUffnHhamr14JQ9LjuJ2QYPokYrBD4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APBDJjfxYAysxoGHsrCWga8uVtWnQoHwhj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APbSwZjZb8DodyJRsXetgEybZBWzwYUWZc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APbUetnvbChZFZA9Sax1J32pWA9DRJzFPB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APbwyPc5kbawdqNm95cFDLKdRrtUVuMfQA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APc1PCY5C85adne9zxVdUihDy2ZKzqvdDD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APcCXHNpjLqfRa9AFy9pv2H5f76TZR69mB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APcDXNnrc5gL1o1x7Px3z56KTZmGky7gCz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APCgeajTakKvMHC1vNH6E4CEqSWtPQGm8g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APCKYpXy5UhPwm4athn1AmCtwRszBpnE3w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APDGHM8oBrq5ZarNa629GLbBuxGjNK3sdu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APdPq3BGJ9aQ7brPDvt5a6cJsmNCfWK9Sr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APDsiXowp37UhvzmsKAQFD1RZeWdE9HXqi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APdx4gwJ1S6DYNgPkvcCQjYVFsbHC3tzgC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APEEnwK7r3F7tm7RcqHrxvbAMbsAVfM6Af") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APerTUZdteX1Deankbz4EyswTHLf5iU9AH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APeSFf9FHsNERTzFvubDggHz7asXDn1kR1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APEtnNYzK31HVSzL6Y4wedz9vTh79mbgHS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APexUYQQ2ir1k5XgeHctfv5dGWyudmZvXT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APeztUkJJiwpXxMgxD7Uk87LCxPJPtNyyi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APF1TW6fy73Tgbcck6bcjV6M7DaruGADSx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APf7VnjdbccEyH1xQcLWVf8U79o7My6oV2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APFdaGvQhHX8jLJs9BkcamMUHVfDAHMJp1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APfhzihRU6xfBazQZuqSTFRP9QPDqDbPah") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APFxmaiKwLsw2r7mjMg5st7tRoW4Sf5E6t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGMcUJ4ZDfK349JqDT8iq2fgYd4AZu91o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGPnH2KBw8ws7YxdqgrGjAZ8vQYi5ym6S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGuCmF6KjqL3NMzBWVUG5LacP7JroHMaM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APgVPVmydL3LkxF6tmXkBqLtrqepeBXdAQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGvR8VmnjFMcoBifjvGuopUYpGsfh7RUa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGXbEFTs82T7rmYs8UFzTHWZoTzfunvU2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APGxN9Txm8v7XmzQ21NhJ7kyvB4NTqKZAg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APgYjEQUSSF8CHgarvu4p6ND5uwkT7Rxqx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APH7xTypTRGASrw7uwfMeBE3oLc9nK2gYZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APhddGDBaARk22KygBz14Q4yef11PvPrUU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APhf8NALd7CHC1Lgo8eTchGGDzdHpwGwK4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APHJb7M2yoywyEUybBqiR1FV3YNDj9iQQF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APHLypPcaZ3RAFEEU7F5hr52Z3ajvCKuas") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APHmgMYEBsXaPhwbacQwS72ZkBUSEVgmd3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APhoBGGM7ftHFCN5ZtbtiszbhLQjmvgcKy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APi7o7WtWUR4qZRtk3yRLYGryBDhieLymQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APif9VZ9SWbvhBpmEza1wNL8S4cCEEyCwJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APiioTF7HBPYonZ6yc5qf2Jcjh41iuVZWR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APJ4uTjHzm6QUggvvLmWczX3DE1zNEKxiX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APj9oc3Fho8jYz9rXeWVG5Awo1NHHHMkk6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APJaTebadCxtkTdencCS2KLw21qLgqfBAt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APjC3MRJU5wp6L7N6ZGQweEE2QDprKc45x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APjhuV4QBfxPvWj5yPZZe5RCi1rbbagijd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APJmyZrxGgHXQsvoFpMgBApcr1rJSKDite") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APJpTqvmxJJStZEveT7Xhjo1J7fMLNgt8v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APJxHVTGc2pMui7doUHd53uaWk6bHc1w7R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APK3KFg7h3XM6pzXiYxfmFMEocBjJyp528") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APk7cuFsswvUChCU6vkeZky3MfwPFFs368") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APKRGVmJxZ1tBSv8B65UYQs7T9ZCDREWdS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APKsk6meaGbuD51bCz4ZiwJ5GktSCbjCo9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APKTeMAFSTZ4rcARoL2USHrvst8fwyWryP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APKVwsLiXJEumN7j79LRezEQTrL7VSDXrq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APL1uhChvFRh3ZtjnztHqreVCXwFyAAgBn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APLCj3x6jHqtFM5nrV3NxceStdpGB7Uc67") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APLDTTHXwcWUQkchBankTqmgn5dkckY4B9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APmDxVCgzauhDGkJ63QJT6Y4dmefbZdt4n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APMThGyqwQmVGvE84z2f1buqLGS6oLps9U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APmUgXKSQruvmaaqhnvmVy5GqkKoyv41ES") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APmYjDnZ6TDNUkvCruGwWzei2Ryw2aaEX3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APMYQskQbTutgMzUJL8ebSxDVhouHfKjpJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APN4HXizFL6wAcPuhFwNd9XVBm5jrcdmn7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APN9NuxDRVNG9EXxxGp4k1ukSi3iFGi6EX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APND5TiejHpk5pPnAMcR3Vhx4pp37VLbiL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APnFNhtiP9qnsPX3TEvVprGAmYNCFQzA86") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APNhECeW6q695imiKaERX7gR7F7BJuMH1U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APnJ2vJWZiEujQqBKLy5M1JMbCue1Aokjz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APNPdrx1oJWmyv3FkEQJojeNXU27n9dwae") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APNRqtx4HPWB3WRh4RMUgQB2Reo3haX4Tm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APNSFXRNLWT1gQDkDoaSwq1dixF8k9wygk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APntqHqY83tqyrNp42z4gFdd8iYkehKw58") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APNwx4nB6GYru7fWP9DKbdWEWrYaSU4Wca") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APo5EyqA9CekPbwaernfnvnGQjxM1KFBVQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APo5zr5PvfCXYLtT3xjrYSfxHaMw6js86X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APoFCuWrTA4VstJ4ovTpYYzCBVMvnsRLzb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APoLhFeefrTryqVFdY4mCNRFRWLBc4kxoQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APoQKfMaND3QoKEhfV8WoYAgT1noiTHWSv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APP1Ron7oqAMuq4VDjsf5ymmRTwkc9AdUM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APpaKX3Rv631VmoaHDnpNgfLVaokek7sgK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPb75CzsVZCSWSZY5BYcWidykHLW9FTYy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPfgkTZF87z5wxESowZTCNGwD3bd3D3R1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APpfznQ7xmui1bcoRWwaEPHeTFkS9dBjqh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPps9SPu4B5n1fQbQE7v8b24jpcrD5dd5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPtEq7Pv8tX2S9Rm8Cdd3TKGBzzhV5fKT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPU1SDz5VwxjxXHJZqHRW8joA8za3wqdA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APpumTt8pBv1VETtA8G46YJKL8q7AfaD23") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APpypVUeGQmjBuguRW3BSJuvrxY3iwSHtg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APpzYwC8xF3NNr4mA8YJ8berA2BQfXEFTL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APPZzCZ9vNZk4bHacDzzdRDSCLHHCK3tXm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APQaq2sM4PBj8jzTcUxH5sYdxxmuHsA4Yp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APqGQKbSyYwsNXSDgHUx28GhBWTjVrC9s1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APQLNH4pnGpBr8y5wQKqTANER74ss6VKar") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APqtzf47LzctfPF6XaZK6pFyC4yrFPyYbY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APr1B8Z7LjcMirpifkxy3Nef1F8GUvNMBc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APr65UaZ8hF6grnYmvHTtVvERA8SkEcE61") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APraafLbTs9MMET8fLJTqFrxghjtGTYAeU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APrgedZYNJNjhxxBmiGbCNUZfGmJc6wRwR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APRtDvk91rxuqCj8zB6nojsPrZTTJR77fR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APrvhcPkJrzcmNBQm3pTQPHVdJLWKfX6Jf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APsCG8XreZHKyYaf5ZdDWtH7oS8etqKTZ3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APsEUuj5CkxnscrTrp9RDvARUKWEvNC73P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APSij6kYwGjy61tGV5pRSvGuTVcdxg6Deu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APSJxyvwJXMH3MGAUrtw8cyngfCcuWyLWK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APsSRGQmorTwuGhWbWb7jueNXr9vcJYHzC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APT43NJfUAY7S9EWjLK74wdDSFRaJMYNuY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APtcG9cDycbnawyDKPX8rTrtXSMHD7V5Zd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APThsMU7pHNmKNPfbgpRrQewx4TkpgrPok") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APTTnBcANLUXZFSrK2NjrZAestzQgx7y3U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APtUCN4QU6gMbtfsemtShLMnT5iECPZuGQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APTYaHjc5jAHb8XoVQmPUvyytJbeYM5y5a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APTz7rCnkYGXzReZ4KyDJpWnCmRg32dJuY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APuBniv26w1PbuaE21E2fMBi19FhNPKans") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APuH8TqyijDfVCvSMJrS92BdtScMDBur3r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APUMtBeEg8U1Rz9iZ9x3BtjJ6Tb4bkBS3s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APUQsNtZDyyKAtLDr2s72eWVCbzZvjqdBY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APutpgMkHRZAy55JzfYzaHGVL1MSiVhA6p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APuTR2ometbvTYnDggTmkfmCaQjurpkKvt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APUyuRS4ADYiWjAjir84sT3LxCFrstRuV6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APVi4HHx7bnjV7r1dCEk3VkWxsgrFo214Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APvtkUFdHWJDLU6tSufq1qFJmxgpJQhW2S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APvz6NSYeZKfHogA6MahgVDV4oAFUm5LtV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APW25BYtiyKVZ5u6hGzuHndNy5ESVT4Anz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APW9f3KqhESEK8Xvjx9zTBqPKShiaMCkd9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APWcdfV9yZSgXWPUTSAW6TccxzKoG2LiVb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APwhJwnyZtMPBQE3H66jrPdhtRpzjy62kQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APWn8jgwfw7dF47FiUxy9eThDmL8Vfmogz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APWTKSmbpBXPkqByjw6pppSMsw1AvuP4dk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APwuPazxm5okcc4kFqqFuuLGbYjZQGTo4h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APwVjLCAKb5VeyHGF9uTJWvSujKnUzNKGD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APwx5FkUPqYTevu21KgRM42cfNHp9GpBqS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APX1RAicNmh99eFWBbrWYipSCiU67Ge6kM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APX6WQqueFbgFYXbtvQrnbUgeYKFGFoZpN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APxDBR3Fw2dud4iwrhB5Lux2aNgHA1xMrN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APXHpdTbXJSjGtq29dyYcYZSyRf61LnPeZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APxSeNZq2smN9MHbg6DhuHMRhja8v94a7a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APXsGiYHiJJXdZVKHHKMBs62ZSTg5yvHjE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APxVcaZUCDC1SgrqvE3f4xTrjdf92Rks9k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APY4SjbE49MZGAVWGA2jyXpFPhrd8EDPy8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APyGZH1tR5VdtaZRAkwGJC8hNQdMdc4aim") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APYKVZwe3bnhwcu1VZpneFHfUKJPfxnS3j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APynD7p3TcLTdzeFvhuv2PfS8u5G2jT95Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APynyrXAcsuDnj7m2psyxP3H3UkBcBWnrs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APZBjjW5TKsSXwbjf8ysvq4UXvP2odPS9T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzcdHefP3emqWUkJ2vbn4eAwrDa7BenCt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzFMvVYW12k97pg7ybYPqj5Hd86qytCAC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APZFzshxRLtWkTz8L4uDihCqCoShVMN5Ti") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APZj1VurgsmP7Z2Khy3Ln3pHxJvmVHsqiP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzJxxKB9CQY4CbPpz4Vpw36ZQX9oAeBzs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzkspCh73ysbkfDXjDE7aFUZkhFLGiBvi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzKYkJjopKLp8TEJmnJBNgXE4Xi9LNXwf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APZMPT4KQp6gX4Z2ADGTECRf1CKLb95Fpk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzp41Ss4r83whn3m1hnv3oncSEEhSgTWP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzqQJ6F2jhYQ2srV8z5mcpFZumfAm81aU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzRr3NQfu4Vm6Ub1WSzaVnXrFC1KexmLh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzRxydJKgnQvtZPY7ewBeaaychbW3np41") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzvHUp1zJFgAnxnQswB52FcGGk2ZvFfL4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APZy8NrFeCdP5iuApKnuFGscjxZnjGnPTC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "APzyEAKUsfjgmL8gT58tYCjA7qG8dgXKcn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ15poKBqoJdsJDYerMH1uRC65VRAQFhbL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ22XKtQSBPMCgWqmkALorUStNAwFEy3XP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ2DSzTRYQWrDoZjMGy9eEkihax5M9RYPP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ2GSqAxyEvgvrjPCUnTH3ghHtvF9bEzVs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ2toNwym8ySNx5Z3ttt8n2Wjh9LLHQS4Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ2xAADYoQLjBhcw6Ui86mkLY3sUrLu3EZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ354As5irRTeArqBK3v5xQpjvJXgewYit") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ4ELYnNoybFroiXgooCQbYxDnsBVGcwtM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ4HjiM89PtdRSuF7UBEZDaFcBPkFHFCK7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ4nxAxYpPP7gNZV25nYmT17ikvnVMVvLx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ57MurqAcvSweoxaeGFySa4xaWZFPJ2Tx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ5gJwttE9DugxbLHiW8AcRs2JKVBEc5BX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ5NZArahJWQSVup3C9sU1DTAGPXBqPGWz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ648ssvLAejrBMu753nes3YUBzgQqq5hN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ6DQVKBoAWMyBb9XGo2Vjju8cYyaDfRrX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ6NZrMajhRszMr6GyvCEshGdEFgMy29tz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ6Q66sd6GdXBVii79otebCoWSeiUsMNqT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ6VkQuZ2G34HmTCsUBPW1wfaXKSx7rq79") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ7CoJtYUmiCv9MFqBJRmoFCerqQ7tbUQD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ7nHDrMARTKFJ29C4sRLZGfDwDbWEen8H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ8Qo9NTRRpTQHAXfpiFdeBLtdzkatM1Gb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ8s2TTasceHWpQoAerWE2aMh2DYxvMhD8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ8SKtmSFcNByJjaYEyKwraUn77UHW9RmD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQ9dFxYgS7pPJT6F1izg3iYjmQYNgedzT4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQA1g16knm6Y9oFgZ76xM3pw9Y16nuWsB2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQAAMHMCyocaqHW5QPF3NVtvHwggcdZSio") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaJkWvspdDkhKv6HjJa4r2YvneW6jQdtJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQapPsViPLdiMZ8yCjcYpKwQAWasQqyjwK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQAreP5jCvGL7pr65sPEWCtkdQUtgFUMTC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaV3MxdWTLHVixurs2uCbKdZ7vSnC4JLi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaVW3jZdVoemMSQvoU9Q61jGJq6qzGKha") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaVznZ9uJ4pjw9LEnSjDJzauXLuLbu9KP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaX92SJPE4uRi46kKiyUxQptU6JW3Fus3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQazpYvdscRCb2r7xvjczsYWVE2t5nxjwa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQaZrV8exUQF9oGogHxHcdQJxrJTPfeKfZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQb1TQ8nU8uakv3Y3uCv9rsecJsCBAvvNr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQbAV5RfXZobrHENqrMxQXT3zVvesCUgbw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQbGuWMVPVhRPtVtwZpGepDEZtFeFFGj4p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQc6S2jqRn7LeVRkPSd7yYhg41Xc4dSSnz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQCD4DxCgvQJYM9mG1XHavDE4s41qC85vp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQCj3eZyKbceCaSfBrmENGQZqujbDG9BjP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQcjfaUQB6nSWGqSzzSmsjNHibDpEFb1vM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQCnPRAunXCHuv34Z9eEdbobpH1cG77vH7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQCUs5kFFmnmKMHxESb5wiD467daYMhh4b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQdphurtmscSqMPrSVS2GFJ2W1XYSxhHeu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQdPvLFUAZYhAeiDRh1fSxvSAh8WTZNRJy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQdpVQiAUxdSp4EbVV56BxJ9gBPvNVYmLv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQdTZtbxDaXYs8x38qWtwzQM4ZXcX5LDkc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQDZF42wsLvZNTpp9pKw9ee7twLhQGGUQ7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQEHnJAvhT96i3pTrvJnDen6B5RUy3Zc8z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQeLpfS95XGypDWD2zGRM8gqLbwYepkc5A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQF85AwUz3h859TyxBW8eSpFh6Ein7vZFu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQfABxgpAsvCS464PiS5BdAx7vnjourZrJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQfip4WkK94asR5sPuCmfdesve4xF3j3Jd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQfMpkKNwRAKrzXWC6Des2ZhVAB4y3k2tD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQFpqpF3bqM1u2LBqv56WmVGfVhS8wFy2q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQFReNGa921hvm2k9vN1Dxo7vmbYz4BztN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQftcBTAXDu9yjVyqrcNMsJzv1iz3LF14U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQFVbu1eYwFAigK7m4Hj34r36D1LTNDbdJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQFVqCGDFgt9mPKgMVfwJWnmncqYSxWfvW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQfyr7oCbytNiTiM5rbhVe4MFgMigf6dQR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQg7Bu7gxevUatPhq9cPUeDN5xvK2AU2Ky") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQGAc6vaP6zHTQMZPm7i27e16FahCoCTb1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQGAweRGX1DMPsik84SkTo5d1mF2tF7WxH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQgxNSV7M3eTN4M6qte9uCjwK1knDmccAa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQh57P4AaJKrEFWM32zGGtpvhHAxsoDpe9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQherQsPcYjcePajkr94F6qgNZAvJhtHp2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQHj22QNo2nLQRPvBAkXfmTvhZDMNerFzf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQHqbxA1kzhT7SrhCiXZwn1xqELzVRYgP1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQhQeHJyvkvh8J9mPDxcrm7RP5fwZQdpn9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQHqwFNirbMUbmkpEo2BYeNBPUGWk9hRPQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQHRF6jd1hgjRGSpHPq9mwcU4b2AANC1DJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQiMHbfvN5uKWsidjiAbpYh1pc2W6WJodp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQioecucvbMTT4n28UXPZ3Pg32tgA4bNRj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQiQpqswSCoVa4nM1gW5G44ch3HEGjp9FQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQJ9ePry45rVSesVyAcKDdXnfR87xLKU82") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQJFJjsyCm5XdSWHdCnQj3v5vspXy3eabn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQJJtZb7SnHCYQSxEF9T4AzbSEqAgv9NCV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQJK3x5PngmMrVsTtqVEgwdCWfvopThFt1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQjQfguKNg1XeiRj2iDEghcW3iSTf94dJT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQJUNuK8p3eq6gTkX5w9K8HLZeQSnftPAb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQjXPVbhZoasXmeWCgLPcpKQPxYTbqA165") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQk4pfthrpuMmgYmJH6TcwEnqLRV8m3Qnh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQKN7haqXXZ1E3w6bQkQZTs83SAcxjV6rF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQksDPpFKwGVh1awrLjguJvzwmCFyALi96") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQL35K1QkzJ3C5awFNUet3BWpov1K6GyQY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQmEHCy6qJLCLetd2iunL35dv2GYhE8d6S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQmFpXHtTLSJMoF7czwEBqj1JsXfvaD5JT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQMMi9swsZrefBQwYr9gf4innZhtkq9kuR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQmqVVdAAWLw9t6Ez3fh5jobyy9fiaphLP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQmTTuYygrwJev4LAa7xF7woyTXgRjHxuV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQMvYVQyYJLLCRfDWqoYy3o6nzdGFgUWPg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQn8czSVUT7z8BaLsjrs7pmkhP6v2q3Een") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQnDSJZL6WEtSGHhPazgxSDYfNymmKHGox") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQNkadf1Fx9xx125tAmSs9axc8EbRhrfLS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQnL1f3YhLMS8qBZ2qtd9CkrY6psAECAC5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQnoS4kqGM2vnwQyvdBFJf189mDX8h6FJs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQnsntZ5jobN9WircDVrh3tdNsAJ1APV1S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQo5kUXCmYDcZQZSx1p6jTGh5Dcinetdi5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQoDR9EC2U2aDGdrNyWkweFSdpi1VP7J3U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQoMDAep3mYLcCRhHuXJvJMdGe8W4TfmeG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQos5ZT3Guvam19WQhboJzRZ7BJ5ubyM1u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQpM3oyKjnv5ezrfpyfs7irbgbf9EDyw57") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQPmtmNSBMLYt81xMA6QC7KR6CjZ64HtnE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQPMtz6fxMBUaJ9eFPLuzEhvXTt51Q5AS5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQpN8DtkDnJfn8YHeeor7p1WyPfJy1k9Zw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQpUF7vGXBVjqADRMdDVLf7f2GxwERKzgt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQpvBqj9Z3E9PbR3nye3qYahBTHzjUSGVa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQQ3ZrByPL6vrdqohLUArsiuDCuuykLiwg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQQMhgBdi8AcsmBiRRr99m2k2nDjR36AKd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQqQ9iqYUHQ3HHRNinToAPCJGnEgVYAvhL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQqRLDn5ADv3CPuE1gMTbo1gNVntcPwj3n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQqsPBjcqhwCFEnTdLdUGHQKGMPZGKwzuK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQQsxc2orZHqyJZpfLKCS8EoCuJDH1xVy1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQQttkJxV7Rb6znrZNHWSRHV2XYR3AubQ7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQr6Qu6ZS2zJiTv6wUTqXw1jXK8wwurpV3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQR7j9bVdUyUP9ZDhhydzm7S9iuF6x3SVU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQrfJMpKh4oxMbG8bqgeE9uXwd6xNWQCCS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQrhYc51bqDZehpvBFimChFyLQQXbTuPeu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQrt39yZAHyrWuAyFbTyjq7jZSeY17fgsD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQrVKMeH8GWV1mWY2Fp4nrFbf1MbcZkUUS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQrzzm34EEMXxHRQGTASvz6KajK7Wkmixf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQSKauUBeXokySoXXG8Wz6JqWdrr8S2iHf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQSKF2xbm4ptNJYQqiiZdjFNn3TaHeY5x9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQSr8SE4q2dGaMM6Z4Zxe5a2iQ8evWh13A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQSSCkoUbkSuW95jLeAQv5RF1TRdXABF6y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQstWdY9H5VAJiUTsakYYKKCG5fny6gdGD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQSvPoTGrjqotDv7pbZTAxNwv4EDCXyngs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQTDsxVZC7UoHLveqqzjs9zW72oQKVCUy2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQtTqzCVoQKjF3DPymSLsmQTp4UXJ27wre") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQufCNw3DrEc52fS6m7sXSqzR6UC1VqNGP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQuPzWzkodb818yvpG6Ljn5xdXDtfUEqSt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQV8KuU6R5owaAEp3PxQRmTDT65ktZkAhQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQvAcNTM1Y7eoRpCWXT3jURvoJ24e22Luz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQVDp9SHeYV1wtBFfE9iQ7EMACGVrZBrSb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQVJqJ1nyz7DegZzqJQo7KJEP9NnFhiNjf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQVnu2ZHykWxSP5goiLUNWpf37wha2n2tG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQW7pB28HCyWvBBx7CXhmk3hUSw82jRhFD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQwTUa2dZncZwiBqdgU4VNySyH7pvZJG1P") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQWW36rERwWz7FhaibsJXbd7vYVwvyVSyP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQxdCBM4N4sarCdeofrCtC5pRXUzrtDqDj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQXnZYGDc4Q1GanExLssAcEiRTqtVGWNVs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQYbWuFXMa8mfLgB8KGZDMU5KAdCXAUZhZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQyePqu9QWkR9NA7ksCFVPxvhvM45xSkrB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQYMqg3Z5dXhw3UZiFcVpJCSn64faECfbC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQYQCnTRKwZ8ibM2E9wDvDJDeWKXmGa9Ta") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQySceKXbjwtP2qd2bXYsQm9ReTGZqDvs6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQYsyYqRd88VKWyp7rq6QeTVo9hSEqakxp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQYvDTxurdC28oPYhE8X8hqTeysedVewu4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQZe4iBERsYfszf93HQ2VbFVTyi9t1X3uK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQZLM8DTxLpA1iBjfrxHwESndyUyyV79Wc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQZPv6sM6jdZDS82pWUEYsN1U4oYCacMvD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQzpZb3PJdBxX8WTpvbz5qpFTSc7wbSHWg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AQzsupHKZPGsqknhjH4DyA31GqWoUM8iFw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR1tPq5zcYhjR2B7rnE2bxofxQiSHQ6vMq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR26FcxFBxnTK4M5n4CQHpArkxu4obY42w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR2d76J2oEdm4KAPujKiupYjcEHZbpKtJf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR2p9GrhTNV8VKUgMVAcNR9VR46vh1mnc5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR2py4VwSehusWohDpFv1Mzqt3xUjWEhet") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR2V4uCDdjZMj1Paf9RLjxhwpgDtU7CWms") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR3GU2DT4yS2z7vWN995ZXCVvhLmvJzdp6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR3KM4YJ35SqvsQYLqSEkdnVHeeiHV3sf2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR3qV8Sr2QVSSRNKQZ8toXgZ1yyydUBE38") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR3vhYMpLMTixqUePjNRixf1Bd4ndKJn9E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR3vrNyrDjDdFJJyCHdvT6u8QYnxcHUkFn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR4PCkpSUBc6ZSrkgYdmTZuQYojFpmMsov") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR4qtc82VM4rDMz8rfMtoFH4C4cvC4qsJ2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR4rg5JU5xLmkTc32qyZTfU96J6Z8zKPXz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR5ayr8jwDXw5hdwA7kUZWD3pjBLbXZv1u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR5KkKqaoZ1dAq2bc7FQqkM7NU8kJst51Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR5rGhccZzq3xGCethi5JkDJ2teK2AeyPk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR7fc9HEJGFHPjmkf7oZ41Vfu8UX8Sw5Ce") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AR8mXAp5ej4Zn1aJpS5sSZUHgEAN3Um7uZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARA7f6bkKwMp67TQUGD2LaQiqN7YJpHyLb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARaabCaQ1QVcU5qFnDVTcweQBDP8ZJzes3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARabzRHCmydF56p2aCZtmdqFhW1ZqYBXEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARaDgDR8z1gZAeS5WEpBVfv6oaAHie2pJs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARaeAm2cQZqjguv4MRBu653j6gfouzyWbF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARAJDGh6hufucpfVfMPBJMwtjt8svF498j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARARW2P5mNJuFhenwV9ezrGfufw7Vb1guL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARawpy9xLGcGX2pjZoAEv4w1Pg9PeNapXH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARB3Psq8EbfPLg4msHDZGVUGj2s8ttwTmU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARBENRQxPB9biMdei4XEsbWoNMudG3ZBnr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARBmbbfNeuEuR9pKyobJB6dacerUFFgcma") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARBpZV5uBDwrng6sBTGtu3TKsqkhqpCrXV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARBuaNwfNXvfnRg4STytboaCGaYcMyUgv9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARbuEiUexUBRwNgzKQMuUe5u5BQqiNFPks") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARC79pkndDgwEDh8LM4D5L8hxbecuCSHmf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARc7mjJ2cefRn3WscZ2C3Za9JQMBPL7DpQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARc7poCVXsM5ji9QUhNsznqSY2YEjaE18p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARCEufWdjgN1hkiypEeC2vsuW7KydkqSU9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARcixVKEShrTnvkgHH8PVMXEgiNhc1VJRW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARcrusetQnJwn9vPEnh7167UK4hTsANRvo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARd3ZqcP2ncSz9PU2MApRsV1Thyraii8gW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARdaZnXSpPNGAEgTYPBNQ4iAKGF4FLKQAS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARDCr3KWaxzcatzNsDGTgF21XcoZjryrjc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARDgJypNXc6PappLBN2R5qDF92th2TY7ze") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARdTGwHF47TmtqxqAawT2FwhSJxXRqXXdr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARdXNAwN6SHtUstBXciFzaNLwgpNwcbE5C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARe4HUFQAps6m5d3tuBqKHumi1iT1ns3cr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARE7A8n7JfitPcd7PAF5Qo2zFkDZDap5Fr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARE7m5RB5ZC3VCbjoBgqqNuhxRtAUHR3kU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AReeYSDEUdXiUjUSAWNsMy9EWFm1r22mwL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AREFQ9U9Hxmin8FXpkT21T3WW4typdPJMo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AREJ8R1v57qRuKrQw1hK2eTCD1FVac16MG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARERKsr5womWfxjmT8zesPrM9G5UubG7xg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARexnhXZDck971pxMTyJjvfP5VNj6uRRFu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AReygXtNV13yoVDSgRM5HKz4uMY1VS6JzZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARFc7CXUFH6VpexvDK44rHVRkGb7fLn2st") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARFL7vJudgim775KkuEPPvBbaFEfVx8pG1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARfqx4HvzRBJnfZHCsaECuwY25ticHdRKA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARFrJaHaq9g2pxg1yorpTbrRtNkgt1zYZX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARFt3Bu3Ey8SVJZzFRM5vuB6WigNovAQJu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARfV8VyFoF9H3MK2bj5HdFBkJ1jxGoKxPH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARfvajgnkWNd8orh6mHtcsJBq4vfatAaQP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARfyYanhtizrC2Qo1yzTMdKwrAoKrRdeND") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARG92G22PDRJgKTcN1MCKDNYC5dXgQBLhD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARgD2ULMBGaPwYiw6dtcBmPSDz9PH2rVK1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARgrGe9VmyGLWSL8fo4vrt6LYezwNbbMEj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARgSiCKV2j5zazidf74krRe8PdjYcgGaH2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARhcXDp36Q3DYpHefek3uQ2Mx1e33tpUST") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARHEoD7FCpm1yGwqFoYm6pQrekeghq2nEZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARHqiuiaRfLgkXtNUGLHADSPjQsn4ws2tR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARhRqr64W2XVNLXCKmaeSMcjay5R36sVvQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARHsdvHZmNXqQjye3zKfEchmer5poLTd5b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARhsuZErgoZuwQjGiTzgnywox2jWU5f5s6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARHVHFLetCYg16fKcLUn6GejnQk8eamC2M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARi3pL6WEMTY3G4G5xcxsn9iyucrQU93o5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARicyQKvkD8bmtrUcaNiBsm9dvUwBp2cb2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARiovp1vT7fLAytUzNXEpcatth8bAkhtpH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARixTqmtMS1J872MP6Jxd6J7VU69t6KBAU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARjDVjwkrXizD5C47iPJ8gJ8Y9JSdy14wW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARJfV9HYvuuFmKHFVjWFkhgWMnJcunYtqq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARJH2bENapQf6eLQS85YShKLgohKKKNhQG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARJszC6YfYFpeKGJnMnQzvFZzbmweRGAP9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARJWnqr1Uos2CfLsWf6Mrh5hBWezCJb2Ki") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARjzGSz6oPBRzdbss5H3EsGZ5Ttz7PqdzM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARkdPrXiWZxPVqiP2f9w5BCsSmznfivFGj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARkes4GSMJGN32b4FCc39KiQCsP8x8WnM2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARkM6SooUDUvbJ1zJ5sAcLth75QQoSEjzD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARkMXWdiq8i94ssQjCH2sqBtBbeLYnHcbX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARKo3j7VXGUVmYuq3T1sn7WJFmqJ32JBUB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARKquyJ6aJbJ4hwVaZHjPrF2ztSe6Hsk1E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARKRZjVtkPxpRe38J6th8nYeNLCY1Q5CC1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARKVaHDM76tQaMJMwEhzKWcec399z1UhAH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARLb6emK3guMhoDxZhpLpwPYdJfCaxBAJA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARLHfdrV6KJpmMxXqsMrwgBH25prh1GWm2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARLihLtc9PwN2arkQCYRpppaDt4QGcdb2A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARLrDMFf3dPa72vHvPMcJSGFgijk5pFvsT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARM2EXfresnj9bb69JzmkF8WBQjKjd4GF1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARMjVPC5UHKkU828xxKqgmAPNi8XC2wbfK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARmm19xirnE3RYhahEfT9BnEAYfiPeNXUz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARmoPtsr6YqUuBDhWDy52iL7zaQaakxUgP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARMQbPF3gjVSdz8b1MfgGyN52nDENytadA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARmqyEwTMyWH6N11bXkFXuERkzez97etM9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARMvcTQBJbNUxa57S5fbghU7xTBNpS6u6G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARnCpYmGJXu8q74PmJUHrfZz3tvALTmkDj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARnNQ571tNbFTTkHVuu58EYqVmF1KKbbTp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARnQhZjVueua65YpN49iL21B36NKM2b2jW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARNUeeToiF6Axk6ryzGcyEGZ5BWxQSpyXU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARnUXdBtJiniCSfsTQyHs1KFVtcaVdL59j") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARNzkiTTptbe66QhuseHPqC1nX9bSaXSAq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoAffnbV5DCLDkESKHehhj3WpL6Nj19m4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoSF6vWFrieLHTzcQQts9TVB8Ko1vVNuo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoY5jV2q8tToAyiUSE1uChvreWipCp7tW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoYaRfL9J38rSoYrTd7KJSGVxiYxypXYw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARoyv8H8yQqT497bw3hPE6RKtcXCJrzixM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARp5xSNpeY5xcoa9ZGzAvsMhXiexcBziwy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARPahxRwtAjGdvJb1vnFT3Roh9ddFR1q2r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARpB3hEC22kEXgmXHAe5ryEW2BPwbYvirL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARpK9mcGznRWXVbabYS8SwDY7Bfm8xniqv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARPokYTwKhm1qdghTFouKgqte1LUNtF11D") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARPWfYhphL1oRb17e2v4gRWFwkMdpjtqfQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARPyHt4m3RJub2y4uC3h1yJQx8pmx5sxQt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARq65PaEqfVeGHweVAf7wsrMdzRAuqQnU6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARQBr2xbUEfqKEeSZBwaWk3GbULKSDQpmt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARQQKkZytbpZE1aTetfttJCzvCunu8GAXH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARqUieWPGwTRC76tZWVBRJmcvg5155L7Hz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARQzwa9Wjds9mcJB1RLF6zzm53znnJsoAu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARrcCdYbns11NvRV6diek9ff3BS8GFb1Gh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARReZgdVnKNm1DkfC2Jbv44dn4c6tAVF8z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARRJNKap4QJFSKVvVonmaxxzUrdmU2cFSr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARRznv6ypwD7Nb5ptLafBMG6x1jsqgj4XV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARS7aJrU8kjjt88Gpn54tL2kvjkxxAVVDK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARsch72U9LUWME7z5Y9E1ZiQwu4MYqLHWp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARSqoBHzgFb8jg6EEwZ6cHwcBPDDcsXAAi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARSRE1BBxcGjkAKTnxbRKybq3dtqr9t1M4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARszwoHqEu6Bo4GQZmaMo71YPkhSc8BGcw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ART1StG12runpvDcuDQ4QjdhXceEwYBGpY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARt8TRQfthhtiB2ctADVWpbrrAS3Gp8T6V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARTD1YKQRgj4tbor9mf16ieA4wQKrWmhL7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARTK26NnuyFxoBXnuph3B2jMJeRN4Bp71M") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARtsFDtxyCpsv3nXSCfTNuwyKsKA5F7Nee") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARtWfFXJCGHoVPKfLnurX5xAt1SvgwqWKg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARtXYiD6APiJmEgAeo774QY2CD3cvuFZfn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARTYj9SwvTMgezv8qP6AacFBap4qhoqS61") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARu8BWU6ZwHzDodcFtzKpb8B46A185XCmM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARuDcBrdrGfCxgTp81LCLD27rN773MTj9w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARUDpzCGRtWmTRgqM5kkJG1MvNVXTWKhza") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARUg785ZEBQ7bzm4qzEZ7EE5eBiTfpNepA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARuhpfXtoGsd2ayXc8zzb8aybtkUnusdh3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARuJWtbygbSbAyhP8TnC2GnMZjnW613ZGd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARumjt5qpZKDVEaJjVJqg3PrB9S4SDjZBi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARUooJkRZDbCGtUbbB1CM1PvVC6S67dcbF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARUoV8NcpoCBotSKqJNgTrUQVewqG2a6RU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARUYNwwWqpLkkf9e4KMB9qkcZWxRwWEwGv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARv7GHHMMownQQa4cJhDsGdaCYLpkbtiPQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARV822qNodpyDBcKYsZADbSiY5Rq8ZRCqX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARV85BpWqjQLGLwA3wXicyGsRvEhg7Av2m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARvbFqS9UrYarZEtWnhJuE3Dj5QC4VNUkC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARVEf88G125EJBhpWQkxs8FKtPbnB9EN1E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARvkkamqBZxRKVrVjJ5QJbHGChDPdCPgNW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARVrwz1J2xKfSQxQTH6FZmyn8GUbE6mtiW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARVvqeVtPM8dEUebJgA2cBoRfHywVSJJsa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARVWSpdNvXWp5taVMRCCsc5ojeCUTXtScT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARvYFZkgoTHfxuwzKUBDHRKFagKaJ9L4Jd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARw9JGhGww1shPoonBMRd1MnEgGi5QEhJa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARWNA2ygS1951kEdmPdh73Uj8Bbvos1G1B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARWNDMs7TtyDMPvkyNzk7ihttCuXbQoYzk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARWnmofGE4yt3JZLdBHLEdQKRg125XBpga") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARwsA3mNAjyjT1ngBb5X9uVb96asLiNodo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARx2KJhMbxTDNVr1buojzAuLWp342G2vDC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARxCj2PGpJur1Lpt1vzGwQgrDMnuBwpSMi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARXiVHA3t4E5MXtKCRWS5zUgUVVmjRPsjt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARXobv6XQud4GxAfCvnH8Br7wCzGnk2jDG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARxvgSEWJ5y63DiueVmKxCsqTHEYuqRNua") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARxXJUyzQxaeyCS6Wp5ANP2x7J9g6TKGNJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARxxRkkMKCCkq1NAQAcEoYGWVfBJWvGHy7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARY2RYm4RhbtZ3eZBwuyB2MjSf6GRy9829") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARY3NNiKJLYVi3HujuRPuJ4e4BwVNW5nqM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARy46cq7yKuAE8zjL5CfaFVF5QMAiusXyS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARYAkif49zJfAZZmh3Tsqh6HTSRQFHN9Tx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARycAU3dxJFJYxA2P6xYT9szQcticTcKvV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARYE5QJMgVeN6BdP6DvyXnwCE125k3Wfrv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARYMq13DdUiudjUPxfEN7ZwE6zsai4nqff") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARyQZfCuFftMkNiBqvyCtfuA81BvYpgM3S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARYxfk1gjLYFrX6eNeCZA4BzkL4anEWv8p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARYz3Px3MxcvwvVnoFiZLwmDF1PJ8RSuvo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARz3Mq41XuGvanUcrLc3h26HvH4UGeCifn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARzksBkJCiy5UCwXP1hdZUewdwVvuSFxBS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ARZZp1NP2qLjhQdhHD8SjtVoELu3rc36sv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS17VcxuPeVYx7ggs3F5hgFh2h83zrWUWJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS1th4KuTTCScoTuCw6GuxXdAvgvZ42r9z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS2D7trnvtTLqDDGPNjhyZFx4EeMFGPArR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS2ismJtsAdPrk7Kcers3RNsVZiPTsDxpo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS3h8RSztGaqkvSAHWEjqGp19cpMLZhCnp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS3jaRBEtc1F4nkgHmR22MNokX6dT5B4Xj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS3RkxMjcEzbZhaMoWC7SEBnSRYoJW1Fxe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS3XsAfbapXukbT8B1U2Bh4Ld6ehwcNNP3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS4o6ERfcvmv3yCZDHeJTuaFwXF1W9Mq7o") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS52JgUzT2nuRJbNJTWcH3rdPCXFBxrESK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS5enPj8FSdk3HnCndToPLr4YjUTSVEnDm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS5rA3fu4MajXobioB8as3qidTWywqV9XM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS6mGLSh5GcxcbUimzaCsoxDjqBUWtJ6jS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS6tQJzuMyRgFoeZKtUavs8VSEjHb4zeH8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS74ntAgHWJXoXh81qvLZZ6oSc5oZQeANq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7Ad8o2LRiei5zQivukJN7PDzomxhJRjh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7gNoqk6NePBM8N7PccYpWBqzKfbiFMWT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7H4w71LBQQGhaChNconaFPA71rL5XdNQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7i5gayQ4BDPGhkondf8pfSBjseZvJdjd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7QKRVVocityNbpy59VXf5Nrd5WN3EwQx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7STVjLafLDm6KuFSEMEFZRuJPaEv9QZA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS7UCmEEgPGC3MqA3thRCZDGU7weJfXwLY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS854Q4t1jfN1BeFxq4kc1sQD2UW355iCY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS9JaVuLCYa9U4DbtFuehkk673VNkHaBNr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AS9rrQ5QhSUoBHiaqR6JSg6RhbhcrrYDJk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASaBqSkVrmw4YM36SmkYZr3Toadf5dqvmH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASAhNmceXsjxYR9wn9EbmXwBjBCJ5VbVQX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASaNFyyAfhy8a9TqnBNrLEqh2RmsvZYh8S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASAPKYGSn8Vd4DEqqG2HVuGh7XAf1k2JJH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASARpfrDtxe66bqh5CxRUpbcc7rUuG86JG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASaswyX6qraxN3kDC9Mdgf2B8JV6juN59y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASAXRgTsoCdVLn87QCn1jgjmjCnZ85uyvv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASaxYYdSMjv8ToMn9h4WpJN9TM4gnHp8oT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASB6WNuJUXpvp3xemDj3XCZ2BU2rxQJD7c") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASBgcJymPGhm5YDSeAbRLrZ5et6biKCc4k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASbmSnsA6yH2uyJgqgJ2aNrdAdu9YmVcEx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASbmzfrTDPDvamxwTBq4YP8M87AtkLvXTi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASCbH9KyLeKtJpfcnE8NLkBn9k8TS4aqWk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASCcb77RFkg8uLEmNXbBKEx2ApRVWemSck") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASCgvbKpfXhRRmbFnmHBRRmwTPkJ1rwk87") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AScKiG3d3ZKCZHaVenq1QS3QG2FheoKfrz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASCpM4qoDNatRZTf1QxSEFBWjYM6EmHQkW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASCUB5iTuBLN1wsRBwFtudieFwM6zracLe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AScYxTCVszV6Pm7vU6meSCUZfcVo2uCMds") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASD3grYtgtg7zEtvKyFPiRruSEdHZqkY6a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASDh7WAWwyA9HeFJWEWstUn2NotTtgGko4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASDoYFmLwUTCaZRyRHfEX1RUZhBuPVMgUo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASDTLoxWSK9rPqCLDyyvBmDHMYynSWGTd6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASDu1Hs1umAzxo2oSSG8URvm4PoHRrU7LH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASdUujpooykub5ZbHSj8iqAhk5u3NMTfL2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASdvRz5ptYuuV7VvHYxyTstE1GvEyZqusk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASdZkVdQhsWrYyZJJphVEzCQxsXdPTr5dQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASDzYuF5Ur4nzWt7y17mbkobmVcVrgNNPb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASe8Z68cSqw466F6YkgjTo5V7qH4FD94Ht") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASedTXJEusnYvHsF8GQSjTuX64eMLyvVyM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASeu3oVrfp9C11E56QCMmjxkHksMRrEoWQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASFerQRNdS6sDKyo4r7US252W3GZ6sEHZ1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASFhgWEycyLpD8RBALeppsZZwMaR8iAMsw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASFsNEUmHPTuUcfthTZkznYRsNroDXFPQ4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASFu1aFZF1CnWBsjYEGmyqsC997s1Pcfqs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASfY4HcUwAqKeqRkCdVdSfE5vPmf2YfCzL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASfyyD47qqssp4uvpkGC6BURyPD8KC4WCL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGA1x4UyHuxoAekqTmjC75YaFZRdWg2AF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGb63csYkBpcucrWxCG7TAW8krwuV9JEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGDCw31rzk56MUs7kFDH8arXX3kDUBhnE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGdzaFUbhrmVw39tytkRZLAA8wdPmhu6s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGerGjjjdXBDxUAQZ45QySSDtdVpqxeVC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASGr9A6yxqBXvMFLjnNE4y3s4ebKzY4QSV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASgXdrmZ3dUF6DejfXgGVoxAyCMx3ZWVHb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASgZeVqZtNmG9APcP9WrquiSxAarsJdx5y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASgZYTVUshYr5R4rCfBNjurdEhuvzC6MWW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASh2Btk8NkyYCcDah9gDvUDTm1QBxfVZuq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AShBVm522pFJ7P3yEgSyNnMgdLAh6vBtfS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AShFb9fxAtLB1AxnnHNziP4LqBNvDnaCsF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASHrPyrFhMv4HsnM9DHk8Lw8cDU1rvDxkG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASHyQNEsUJWPn6TCNUNoYYVvCKTpzXLks4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AShzGLsaZ84EdxVqAK27cABTt9v646mCT9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASiShhbnLuAKs2rXZjq33epV6oB6jPtLJp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASix2nFFUDRe8jN32tQ43bKNxBJYJY4x1q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASJ3uejHiDDCahb16foUcWZMp4wC6qt5FV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASj4Hz71ipgdEWiGPSoQv2Q6XUmRJdHEm1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASJgzdSzqmQMGSq49UN4f3vYWbENEN4qmW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASjHjEDweDmwjtpuWnjir5fJGRQ1Gv1bcH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASjJs1oq7FLd9vfgDNP5JhNxMEWuVaUpJd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASJQaSkTQHtiYcP8Vn8L4PPe5ysmNrd7DD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASJSEPwUE9rB4TZVAHq2t4tQtiDYsRgJeR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASkQxaum37vSXdhUmXc5wmmf7fuTrkfczg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASLXAjNAg2ZoeznAJGFrh1oJi9aC28e456") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASMhhwJyFyt37HsQGx511oRvm7vrVvWdad") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASMoWav2mPdNm9q5H4WzNNW1mWwkvEERTh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASmRAxEBtQGaMwNF5dSmyhjtNvBCo9G3eC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASmuijwFJC65cbamMPJ4YNgwapagYEvLcr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASmupGHrzpd4KBsUVBQLaQcu3fP8NUMpaP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASNEvB5hTYzDZSqHestVjQKHCakxCJiqj3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASNGYh5dBMTwaqDyhiVVQG5miQz7xdK7kZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASnhMF6CwXpbm97VgBakVGYnSqTcn8Bkac") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASNtzwFDBjdSnbxL2qCPZBzNo6TtSNCUoi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASNUUEozsCZzxXvRA4DjSqin9jwEToWX2N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASnZN9xXkAUSSjmazbbGnsZ3E8XscmYiaR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASo9Xvm4fxrbGktnFzy8h7v1hMgyBsBgew") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASodHwTfvKRvq8ZxPLrQDheC9sYuPYzxBg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASoKf4tkutZFZb4EcBMdJzyeQPCXBi4C1B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASoQbYMoJ7Ggm3EkBq3aWVMGVFpyzzT6GC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASp1hSZoCMEgWshEjB4yvBPmbS3Fk2twxM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASp56aUPqaQBBb585viwg2cjW1DMwWjuZ7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASp8h1YBRuMU5fmogYic2ucke81ioCT1em") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASPr68UwgzWJ7iw1WJjTz2u3trVjaNTzo9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASPYCWUswxHtuM9DgNmAC6G1krPH5LGK8z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASq4mZGKY9K7PtuCcHRr8EGGjd1NSTDCYP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASQAhvRjw6eDkrqyq9qMt1QE4rGjBsnapL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASQZoDnUTaHXusWBRJRwptjkZu8vWLKYBa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASR5xV3uz2kEHvCfoAgvmERV9GUs2g4RYd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASr92yETWv6PQA27Z2P8ZzGBy2g6qJbTEc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASrEVFmRAdSxAsazpUw5AGL7nuoTmkzk49") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASrj9m2B7j4XT7DPEx9jx4p3WFKKLWgACF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASRnGcumkbz34pvQLZeJuxqH26CjAMEUWw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASRqUGoBMFCqLuaxjuMZK3drKVkYt7rYSo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASrUcYNKfhQW5sMW1y57R3RAan8wRCirgp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASrZq9YevbYMYEdQaQR1vDqJCAAkuw6s4s") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASS9ShDN9oMgd22rz5Vc933BWkNiGiFDvJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASsfKrQ6fHtnmbdddYmKCfNvBK22myUUdF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASsG8wrSo7cXKjG5m4fZz3EgrWpCW1SovU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASSJpNwUjmr2fz2N2RRC6vYU7Y7TbZUp1N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASSQbh7xrJdvb7bo4HpsniTYxpxcZZQFUr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASSWvMMUx17LxUbvArtMnHHyoK3Jvjf1UW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASt1PGvZvxCNQKJj4KexnKv9bFwTYDeCu2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASt8kWNudLWVm3FdS49Jzj3H7ysGYXFpF2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AStCu92c2XR3HcZAK5F4h4US4EMaPPNQ4h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASTddNcK9qP8nCEqKUTzEQaq5gtEti5oAh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASti4xXxJUUX9hh2dAzaoGxuRUct1Lm5Rn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASTnP5BkouGkPYbm5NPpdQ2WBZPKzR5Up9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASTtg28Ek3uau4ajDooHWrE4jwJCvLgxfJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASTwVYFzxbXfg1umZKNd6Ax7w2kWyzPgGM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASuDzijD8iM8W3wjVEbLPjkYkU2QyyUjdi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASuiWJx2tysmzDm3EcXG1mCc5sop6QA8X8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASuKuMvZdTVP6pfFCVZU2iqjNTCzt4k1X7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASUwBQ9mFjbyJ3cXsLRfwup5mqePrxYWRh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASv5j8tnbhM2nwU2AD74GjxLLVmVqcghTJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASv8UPTiqX8bayUYHfVNBKipWaeYyVnW1d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASviLRYxMiXxPvW3SbCjsEPhe9oLCzQHrY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASVTRqbESWky1xu2MTHXo177uB5k175Erq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASvvmzMdBuetWPRkaJjC26Q6Lcf2NWkF4v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASVz4eay1hVj7enNuu8Cs3ho9MEA8GG4VH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASw6f3WmhMihXh1kAssgtgnC3HuQYbsEwR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASw9gJaeT9bU7vmKvXyyYDcFCUmmHwztwW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASwvZDcCa5btZwxNW7xk3t5dYxZpUjiSKn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASX8CjtbWnCqXvV31rtixhyiCrjcuFqvZH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASX9RqyacPT5LRKdjWPinNmDD4LEnacDf2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASXAcgz4WuduhrkYRTRxg9PbZCoJjkjQmr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASXdo6bd6qUujgimykwjVvcyX7YbzmyVU4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASXM5oRa6P8Di7tKuvsvTT7mbSMkikxfPK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASxzH3FQEXgdnMNQmTpW5Bov9KviASivvJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASydtvqGhD3aGVJ73sctPDoEUFHmNPexKo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASyHndcNoZrE69iqotZiV1cHfUstdvLmt2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASyhzKXuH6ZoyRT29YnFiRsWBiqbVk8ZYX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASyJH8fQvyMifeBcktpYvavKGtC1NHawit") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASywthKajuYoRVFP8eRA5L9HAYWfzyoeVQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASyzXPaQdv3APuiwmASf4BMxRBxk8aJ1oK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASZ1cAMzjgLvzCBEsH3ErLvfcBcq2Qgg6f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASz5WSwHHiCPndY85LwapYRXxdohp5TkM7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASZbi6pad2qSv4DS3PKPXset4qX63Y9rmz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASZhdxSzMBs3DAAHNRegQ6a8qqBJFryuFj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ASzmjZkpVCWn5VJHxiwUn4rzDDP44p63DP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT1jrZtaYF3YEhgXtihoyYcMUaf35z4GSs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT2m1rwCbXunW5pSiLJuUeZdB9K6KDzpYE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT3MfDhGfoVKZ6qqzJzwwsptMJU9iPkHWs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT3RpuXSavbUNypmPw2aLaS2Yh4kEisDDn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT4oMsqGXdTrZaqaeYm9DN5NkWjobF77dg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT4UXU5JMkPoSKc3MnaLTPSb9FTYDQMmmH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT5HCEbHYQi4o8DuX2oAooujcRfDQACNWT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT5KqMida3nzTbBY6Fc2QBabWsQ7w6XEEg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT5mXbW7osmACvYyGH9HRfuFZAixUAEaQm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT5P2x5ZrcNtQMZ2fWxrQ8waiLYv5a4bhf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT5TXvK6s5cDZzYQsCUGsdGnRN6VsuSEwR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT71RoAU9sdA6zYum8UdK1b4wzVA3r3QLf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT7SK5xdPhd66UqNkNBKmKFfXxdqPu13B7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT7wxzsyPoHNKAzoyu6ofvLKiU2FGGZwvm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT8tbaD3vpH7wz6Yw8iNbH4ZyN7SvWS8px") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT97P1opmMHmrqX7MS9gqp6RuF2C5pgTsc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT9t4duWwa8fRnMQmHaz3ZJLzYaqyUo6Cg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AT9undynPdpXJVhQQsfD9th68QBPJYkNTD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATAdwS9Je3GNdmGBGV56fhi8J6d787N1ZF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATAFpQto3g5rtM1vCXncrW75vzzX9yHFsB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATaLYZAMvs4Gc7WqU2Zw8E38WvdFTZZBVm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATaNUUvezx3qnGkhT4ZegEdjquxCyHBx4C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATar5bvaVGHDi3i8dZBoGtAomukRxAcAHU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATAyxdKq9es5cwd2Z7yPnLNWd9ZF4CVbfW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATB1kpThLxn8QvQZekwWbrrRgKzGNRw3o7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATbmZLnUMUjUg5xTMuHjpuPZPw33VX7fVy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATbreWmW8qcu1sN3exVSaHEBdQ9opj4FVL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATBwKQ6hxNtGF8hyLk9jcVKBMXHK1phuMU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATbXpofM1bvKkqvQNk5cjvXxEGnwJSEmCm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATc32b5xUAhFVWLpxaFs3v4hJBVTxzpMA6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATCDSEqBZDXnUptBtiJcsF5J4M437zRHWU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATcDST31nmw6u5yCEb6yS4nU1GaYcPsQG7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATCEdFrTzU2YfczZwVefcm9ermf3ixBhS9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATcEpsCYdG2c6917E2YekFAi77JLUwmNnf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATchmpYkbeG8k5gjUVNqUNn9cJfA5MJyeK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATcMqLTWhSHV4obKiu2bAtFV3vZiTeGEie") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATCPaNKGsreRPk9EQugDLwhKaQoTcG7JyE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATCRNiHq7BQsbdP1xdfWgcQnehjkyp2jGA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATD85dx1uyx66m1ALxdLyhfHf5vwN48Ftm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATddfzyET5vaCRfhFPYEgYon8duTPQBKwv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATDHwgSjF5jL6QrXdtuha2h5zfBNSXNzMu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATDKwV7cUG66yDy7DJJKgNEEmb5sVRCWEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATe4u1Rk5LkNpARQCHkxz8rb9YXhCCYcZC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATe9Fo4MJKY6VAhgqEqGLndsMzC8sEpsXy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATem35AWx5NJEW7G3U8vF1efbyw8ZbL4Yr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATePi1E5PMMWTmRRvNkD3uKFqrfNNf3yJ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATEqZ2iQC1vzSuXwaDzp8fjbqnKSraGhSJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATesSkSF5SDEpGwoJLUwNx33xu8ruKiF9i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATEWgDXw17tTMuPrF3J2mPs9KhZ2jKWt8b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATf4eHKUmb9XQoDh8ZQ4BbjSWA1t3qMcw1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATF5c3iW4BHPwaBi3pnrBcojNjqcRLK7dW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfBP3dmJG5au5yy9vqM68ywehKQJBR4t9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfbT3Cm99TzS33fLVyGDkpAcKP5c5RC1Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfh8v1DDZMSAshqP7A2B2A4ueW9epBsMs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfqVCrjHFyvA5aCifbZe7YNuqEKV52jFH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfxZEVBfGDA1hCfM1vpuWMd5YLFwdhbnS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATfYgAcBTp357hvHsbB9VxRZoTT4Y3MpcZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATg3Cg1AgUe8AniGdqAeip6kM34v9r3HWP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATg87DLX2ob9GGnWEG2t9sc1ao8M5rMPYh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATG9HYgZfYURgKdHMmNyifESsDF8Qrecav") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATgA32rhP8SBUgKcxnUTSPEqbkenbLC2eQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATGfpqwDrpM4yMUH2RuqKr7Nxzua7MjF7k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATgQaGfmxGoF3cgRhi8y47TJNVeXM1zkZN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATgvVwdkNeyFL5Q9sz6AL1c8Sx7AWQ5GeC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATGzNbVc9E54Zcv89rPTmki35Nsu1rvS97") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATgzQZqiFn1EwwTkELbqDUN4eqCCxtog7N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATH28N1kLeVj4QRzZxQv1MjYWSBEX2d8xq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATH2Aq8x2gdN926bEj9ULrY61dpucnXkzq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AThcfbiwFCPGqka6q5csSDwBx9yZK3wvpX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATHjyoK3CWgtNVee98xcdiAX84Cp1qhw7K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATHMUCYU8HLPj6V3T86Ej1xUL7uz8e7sbb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AThNSJT3nR34Thej55qZqoN84KoN3tApr6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATi7Ye3QKTpzzXtEyZ4yYBXLYD6VdgNkAo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATiLAvfrT5k2G3F7nYPuePK3E9Wm56xkA5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATj2mpBZEPgFjQ42HXqt5eAMgAi9pzfqUp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATJDZrrEFYjRD5kJ6La57scnY6JiDAucdG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATJGncTDgcQrcBENbCRnQvoVrAMP83yvDR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATK4yv3QXANMazvzxFkL11YRvXwnGPpcom") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATkG97ZAPiweD2KvHAt7dEfrcduetQX64z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATKKjjEtwZnVha34gYB5gZWHhiFYwTgz8m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATKMdjwGfTdEUBWkRguPtpSqoVS7vwTrwt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATKQyC54DjsdyPZioGM3sXE4K2RrNBKA8q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATL5YkLp91B1iMJSf4XR2Ytkaiicv44bNa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATLMFv52GeRkoLXyWsVrqFBnwUrd1fUPU6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATLMZxo4mxavpcNepC9wmb9k9tt6GSxtHN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATLXVXwt9TAwfojnfPyJ5LYXcShfqn6PVt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATmgQZGDJ9rcM4FgZFADR2GZs2dAtp8eug") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATmmhQmCFyC7fmYqcEKULApMhgZqPsuMFm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATmt3Gi8k2W4BJrWqvjdq1bz9vHqBB554C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATmtZhGjTehp6LfZnREWCDS5SHSLeTKCW1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATmzShtUZViUpLwFwhFHh9bBkyk8FDgW7f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATn1L5vj87A7sqsP3L9pSWUFbuHYYNfQQk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATnAx1ejD85wySwkKQZPboP7Lj7aE6jwAP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATNkKZvYthhCFAA1pAkUNAeULPfw7MDdV4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATnPbHPk31dXd7mpYnemdAPZMfjnGcoH4K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATNuDMCLkNVJKHvm844bgo1moZtvS5wXH3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AToiyNfSXLqjzRcSDRvRyDkMwELqYQXEcJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AToVA2WFSVRBSThHkcmMU6ViTb21uqYhZr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATPc5NCoYSbFF8vH24XmyEZToj1ydWiroZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATPCcWiC2mbbacnFbPcRTu9ms87fU1JoVf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATPExRravJ7AFFRdbbJM7smeVYoExNUNxR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATPWW3CiAMa6LYBY5mHsQnAuM6kL3CQ1LN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATQ8GWx3TrcxqVz4HML7ghnTnKFuvzzkZ6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATQbUzhrq1YW2WRLQCwPfq2n2BNXs6NTwW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATQqpqduS1qv8vAVoguQJvXHEyz4fyPegC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATqVs1BRcFwHdcXz7siWef4DwtV77nmvaE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATQxLEnEJ1KGwygVM93dgAXSE54MPU92yQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATr3V3STaL2u17DLdQ3FKMuyRaTFoRv2EL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATRAxn869eqTr4vp1fue2WG7UsjtC5wsQ1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATrdcD7jvNDkzmYbYzyQZd6tJ9RCMzWVRp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATre3U5LgPxeKcVf3N96PZgv49Gr7QCx2q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATreU2FzZugbWRaZydS7KzX1Md6uTE6ryb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATrF7B5GeJ5RpHkRdV5LH4q3j4SW6toEJL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATrQF5Noc7bGWVbqSQBqrXSvb2sPQnMBNR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATrQLc5iRBa7K77pmuoNEZER6rAt3Rsqc2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATsBa1praf2Wsztf98hqdh9382XKZmZWzC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATSMAqN1AtckjK9r7ER53kYbo5nSGBejNH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATsmWnbrkwKs3TifrqNGwUbqmsJjmBgdFG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATSPKUxaubZNM7WHmaLXyNmnTvkNVXV9Vv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATSwV6HvvYikvLh6DRXcZGixJyst9nuf7Q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATSZo9nvRW9AWPC2rWMJko8EkeCDUWCUiG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATsZR6zB7o2oe3dSeY5ouoJY4jzX9TMmJL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATT1B5myr7y1Ny4Xtv8SmryHdZHpVpc9yX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATtDbTAvAPfi9AC6oyjBxEW7oiKHtBi5bL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATtevDKyPMWMGCAi9P9LRZfnWKbUrmj3rA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATTodY73bkgXggWaJ335ypwftdxKmyMgHb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATu3iwb1VAJ74qQW5uYHxgoNUGsfzbqwHs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATu5Eq8yNDiptnjnW3NdSHojhGWGKkzf2G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATU5wRhqLMMhZ1etrK2wL7FjgWDVFg3NUt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATUGoGA2KSMedStNPScBohioMfa7oLXDS6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATULae4hoNSy2k3eMtsgd1k12sd7gTprM7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATuNWMdv5x88BFiukhvD36myi5STtrE6go") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATuZVZfr8SAGSNFxmw7HhtBQeBdThPfnLc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATV6jQy41ez5Q2ERo1bjVqZb4Bx6K4VYKK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATvorHfgbYet39R6Bvc52c4mdygtJW3kb9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATvsG6pHVGxUcBbYBBPbn32gS37e6qztBR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATVt7msUnRqQGHWVmhx86nVojQVyjajZMc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATvTiTrWNrqfosD7hSYuercfRru6DCEJiS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATvtnwocwkzFmdCzYUJAhnLnpqz6YtZyft") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATw2EvtUz3VVDmrAEpX2SC5W7YFcNZ1fQi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATW7wE1bhXrW5FbMFwrqLyJGjeWoG2DXJS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATw9ngnB4XAt1xFyTS298SutvDrLiBAJF1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATwGQ9Zq3CTpEV6G72VuvfxrXiqkcWrC3i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATwjqJ1yKLswMxWMAgkePYsS5f1Dm3JTgD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATWMueJeY4ZfwTjoeqtYtXq4gCYbeGzRvm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATwVNESQV8seFC66zZvq1HSDbyr1h8cGmY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATwx6gMzC1p2nGtVMnAWi49Ahxr4zLJ76b") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATWXEJq9kHzRZkrEkjy4BviHC2rpcx44T1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATwzMqu473x3Ht1AdC5HmwVYh3A3w3RBpK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATWZQGJoujJ8RyGXBWUg6DPzDpincsdrya") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATX2wNmavcT26DHaXYy7nsw9nxdw6tqbsy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATX4gYWv4femzTaHdTuruDfzCQDqvGGKXC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATXEyzgLQ6WhjpBBgdtKyKASPp93oogK8G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATXo7XhGWXBAmzXzeB5S3qZN7oPKzH4tUW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATxUPbWGX71b9vhTSVKbqchaiQ9eHAAxQt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATyBd9H92MRdcbL16ac1Rb6AL62XenST2A") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATycywFh3iRLf4So4VV6XT8SftjFnVknaH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATyQoDscQqu4fnnPeHL5hrESw7feqBQW5H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATYtgzgndV6t8nFePXS4d4kqDUQ6MXx7t3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATYXqR2VSy9R83YKTa2rDxmmwfNidTwTKV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATYyvs9D4m9CN1NR8XDxEB8ozBUBwTjpqk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATZ5LTeKSouRhGVHyHCvcd4epohuRgVvDA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATz5PVtxCVmCf32nkxugPo82adwHb2KAaj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATZbwyMV7kMf2DecPmCkojZ2YsT9LLLeEb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATzckkjUjaqgBNFcPwanfNHbdM93dTF7BG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATzCpYEywK9XtA8QeEDG9rqff1cxmGCYTS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "ATzgBdgi6gwFEcN3652j4DiogPibAGSvrJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU2hiefMWZ59tvKk5KJY4UoVsHdKkDAfgU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU3joSEALWGtTvkBPKNDMZKomMj1yC5fjc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU3pY4z9UnZXg2oKzf5vqezh19fxmnas38") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU4SUmcmWrz6ttbBqjFNg8mmQMs9QB3S97") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU5bGK7JBaie42HKWjMzCNnmLLZBtbesUT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU5DaKZbSZGF8ad1MuVP7AMZhr7Y3kHZTs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU5fcr69FGVrxp8cY41ACs2HV4PZfQxsnV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU5hKxL6dGuNMqEJmQkS7srRsWyoP31tSc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU6cw2bML1GQnqEvpexdRPb6RhWzVk1Bzw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU6i3dun9QHLNzaXXS74c2y9LyNjhtuad3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU7uEZYkkLGBNjrGtabMVFkheMXxZyRbQG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU7XbSrg5URCoRGimSv3DgfUb4dk4zJSar") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU7ykdsjGkHR2C7U61MUWtWweFNT33Hmc8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU7ZpvvNcg9US51AYficNY3MnNVHV7t8xd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU82iEXUbyTRKbWq9ZWkaDbSJHSCcCbqNi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU87kSM4xLBx2yT3PhvyQaPocHec4ghcwR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU8nTbqkBuAmzi769nLYjkfteKru5mKmxY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU8ocMRxGCYE6FhMUsyXRXvUuc3sisMFKh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU8oLFXEmWHMauvVWWzHdSMiYJ6zpm2DiR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU8smBKbVDMUBMLvGcYHiEauKXttzXieyZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU993km9qYLo1nngubywtNEwvBG5iVQGZU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AU9FzMeHddK6vpsTpXBysYB4mDBoMrKwzh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUA44fjABrfRKi1QgrwSXy37R9Vv3JRQTo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUA9H3gpnBKz6iF8YD9Vkfz5xeNdnsGKHo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUAtTpU1rYwBv76dvpLhHHVBdT5FfrgUSu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUb3uZ89Y1izKe3uktBoxtWnHFT1y6ajfp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUbES6tbzdJNsEsZTZy1bp3GyYpViFsaf9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUbiAqHEDTX23QqDd9WBXw1qXkXr6ooQwm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUbirw6vrVtSejHdYMnTBszM7uFSsQuh3G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUbjxdJGh9xcH5H2pmcA3Y1wejfBBe2n6Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUBJXjNmTc1Nf1nJTCeqwgpkXwGxb7xPdv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUBxfD8Sdo7uuy2e2YZnycc72agqBSH3jU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUc8eirJc8eUCXLf8LC8Bujhq6RjbPTE4C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUC9BqC4JfUqbPsgSp4MMnyT5w8FgB5Apt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUcDrFmDUymGxJe2j6RsffFcUhvtfg9pbs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUCJP9ZrXZm28ETgBkJ1E3hqhYudiFiWt7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUcMx5u3LkhWnoGwqM7nB5hzRsW1aMhCHe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUcujm5sCBX1rVq5Kk9RJR2NxLWTB2mwZc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUcwFcZv1LAaV95YtGxT1zy55gVCLUVYqj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUcYpLzKyqkV9ReSezzrGUWmXauHstLLKj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUD3P2v2iQ1dVUwETyTwmyCamzXyLsubfc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUd5TL4xY6aPJQTpUbvTDt9wihk8g2LiZz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUdESHwnpvcH2kXmgW1buX853HhKA2waA5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUDiagWp3xG5zYvJSjJ8Bcg4ErtLzxtb5R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUDubWGgNbnDQe67VfSTt1U9VnqWGQ29de") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUdviCmr2XyddivPijPahQ33rRHsAffcyY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUdvkiT2KK2dH8RbQfiP7haQ4gxEqB6MXY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUe1w43fRyGPS5yyKEsuDzGjA92zggakFx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUe7xjpGPupJhqgv9X8Pu564PspgEfPCUh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUeaiLEMeRXsGYGDz9b1qxx56NjTgmKTzH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUEb6oWQ7FNMM6ZhGVC7ogkbwBjRYu1RG7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUegGUMncG3wAxpgmHizzYZFuTebWhmAYN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUeSMM9jELYPY9kbxfU3f2jRUYDD2jNiqN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUeSqmUN41DAFZqK62XMHrsYQR35e7Xvwy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUEZCtFiooGKUsrMQDAfDWqi8YkqVsRnPY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUF6UYk1N256ioBUhiwCc86ZCH6bSASQg1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUFbxNcv9jLb6gLbt62y7VzHbhVmnjhFQX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUfiKUNE8FnQF4eYQK8nhmrFwW6u1DTag6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUfQEvv6xQ8kTWFx7rj5ZWnb16Xn5gmuup") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUFRQY7nYTyisLuuuWFzb39hUNcpULaAiR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUFWTXbQufvnYqHPvCtqDa3HtwJHyY3LLA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUg9mfo9YDNUqDAR5bqZWqshCLoszpTRYP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGfQFqe22yfbDyzSuyad6cAZtkr9PnhEw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGkjHFnnrC7aWnHcNjNivfscmSNuNLKw2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGpzuHtLNkUNr8mNmPfEGqRdMewnbMiJc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGSMdnwptXs841HySvMoyoQB8XU8a6Huo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGX3RWdZxegJW5KEerPHCm65cC1Bzxud8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGXp4HUssWY3QNUcZrn7jswYiX4X77syv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUGYpEA27yhy25gyaWiSpTtAsB35tvDYic") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUgZMv2wJRw5a9tmaphpSc1q6bsZsW2MLL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUHaUPWPh4v8Hc5fAPMJTk2rJotoSsmb3F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUHDApySowWbFY5Km1QDN1ScENX37yWFBQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUhFSQS3a1snyjbhRnxTEDaVxRWBDTJg8k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUhLdTtbTiQjqAQACrmfUpktuPJVFMydax") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUhSvaD9wfAb4ymTGfk6JSRX1SP16SHrjZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUHzt6kCEsL6eGLbdzunZcnW71SHt8mTVD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUi9R8YQnxGPWVDbfukh5L7fpJ83CoM8dz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUieCx2f8i4wHQLAwcrD8TZaYBHbhhBESS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUiLJYwV54ShA69oous7NXx1BuoqyBCGnv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUiX1DjRzqhQ8MK4ELD8bHuMMoLHf6v99i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUj1k4dqrw224FaW9Wj8ZWCaYXapYoQzgT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUjGrMa7sTH1i6nwCt8r8peDimLd2oFXWb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUji8PNQj7Abr7sTaUikba81GLupKKP2ii") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUjsT1ya8QBjaZHze1bj6MttUQndnZ1eCw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUJTviCTRZnZfBpYP595QoH9RqEDCK48sK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUjVsKwBQNRgSQ7FbHsoM74Dc7XEnAnRWL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUkCc9E9uvAY8wbPcohxZKpjCdRpD4nESz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUkRxEuN6e4QGsqJ6ePTc9RbGTYmQJcfwV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUKSUsoyrVo84wPcyfU3ZUKQKny49Dvwzs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUKUmkRaNUvjQrrbobgfmM5sQLen1aZetP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUKVAZHvrbHMxL6VA5qAny6XcEw1knPvXQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUL6ADJbotRiN1qKxTYYgyiHjaTumJbw9Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULeZPHPEr5kiZfH8TeGpDc6XZxL3N9CFj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULJrtE7F3pp5MSM2cH8PkrxKsT8XafEFw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULmN2hjpkxJhV7fM7iuFm8YP4oKCLBJMw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULtdWhwnRgkXFgiQURjzEy7VKnhwfy3B2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULwLGMeXRuZKBuxMtPU8uHH3Qvq2V4KDQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AULZVMBEeunHcHWLjzAxr3a2NLmqsbMBMv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUm3gcbEDuxasHNDo5CDq3fqiXbwGFwfqW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUmaBWZ6pS22ZVKTMgwZECL2Qp9sqVAvWn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUmBeNen69o8iGnHM2o3XZXbanv6tqzCy7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUmeCCTw5AmKqmmGJJxgdbQY6JiZVwsW3a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUMt125gJ54jE5PTkkY7c9Y3nVW1f33WqF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUN5V366mgYpygVrdDxNSPszEG4RtQNyP7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUN7e6XurUgHBxWFrx4LodCuxpKgAcRafC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUn9Tid7nMF3SJKpJQcTUFZZ11VxkSC7c6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUNCDFQVSW5YQvLEcc4tTYgsiqHV2cZiDC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUnDRdw4Z9vPuX4jXiU7EACfbGWXxBFbnz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUNg5fJzjEyzcGc3NT5sr8uyVqYZQe9NMV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUnm3dkpdxdDKZUnnVaD346pUibB1Q3Yq2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUNMhfNG78DqNR67uMoNA12ZBFJGb7NE6h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUnNGFdSPfWC1avR2ZQUvof2gkhu2fHJ35") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUnQEW1WWBwFEq14tekjhqJ2KGvWZjv8Ee") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUnVouL3CcX636mxsM7nQiZ31NmRqMfF5S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUocJmSuUSSEoj1xJpTTjEeh1k6xdL7b7W") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUpETg2dS2mfhg3vF3zDNZfSE7SsU3sXba") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUpNoY39NaL3aMDepZDuTVhPCUf7drtTVU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUq8YshD5dvpbZepU2uBf8VXxU66KeHQSM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUQXAqKDeQbfUoBxVtw8UqQVQbB8zbSDhX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUR9aD6anKc1wtNCYPmK7697oaiABhZ7ZW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AURCbabmQxd84tn7iDvJaLytm2HQKaSyzP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUrjQsNdVoejQwHjTu5uT2bVsTDTuPmTjT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUrwicDcEuaN9Zg3WQteEK68nxzXAcuHzF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUS3ghWir9KLquh9KSyyGGQzqg3bgZARPk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUSaLF79SJL87V89b1AWLkT8DPgyRcBQiE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUsMwKn67HXS5CeCzm2G5WbiRfmoAdD92G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUt2qzdYrw3PpKmLcxH3vzkgSSqT1S2LsN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUt3MGDrrcc7cWUK1jZArbLVtXJHDUk5Jv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUT4xLxPZNBND8TP2FPzFxgWxVxd4W7GJr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTAUUiYdyHDZAPKyjAUThq8TsWzRurEk4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTCLgXYKGt42j2ek915GQfArBxXi53e3g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUtDnN8sbHdxSJ9CFvPU3MRwoH2PhgyYg9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTfnPwx86MTbAQkQszztFnkvTyXDRWKYc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTHeBFnGF3r16sTaKjhNfEot2eu6qBACc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTJ6DjnSe7JYDEfFf4RJ4JwZ72FsbWHH4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUtKDcK1fcvfMoWoAEyG3VNFngs8FPo2QH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUtkk2d8nhmFPs6kocczBjzgGpYxTvV3C4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUtsYGk4cKrBpYCSF4vqaB7UPe2gFN1vvE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUTybPr7nFvybHGjaDSLHboVaHFhrvFgjN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUu7wDvSigA3jtLV8nHov6LBPKymhXcYPE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUuhG4vZgHyLEvXReiKhdQaY2f1WXHVJRw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUUkQA9FgZd4EYxL77L2egFxCWkk3xafGt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUUvSu8ATuoLnDT3rShBLz6Pe13hrLPfLU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUV18ttusqtLwu4HLQ6BpFrDUBnQbxhQA5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUvabRbcxFLKaC4xpZchhZ3KWHFC7Dqvu6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUVCJrQX51CnFQuigJ9RK5dxwEmHgrABTq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUvLQjL7GRVZSgiov5Wqbjmd8eMoQZr1Ex") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUVNg586VuvoC142FvKG4iteuL7aCikViA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUVVdCzb3BBrHU6Z83kkzA32vT6VexwJ42") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUw7Dtbn1Gb91aDaMEHxraWffw7Mu9HV81") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUw7UWFT2UG89gddRnvXRcyXMF4Riz37MH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUW9hhGKPQ427SxmVAnUgRbbeuFFuMdKdp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUwaiRAeGM8DR2aRDrcTkn6r9mwUo1kebv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUWtU3ssWWvwphujTXqbJXuZkWKnhEou6a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUwZuZ8QSfuDh374AKTdpT9QjAnJd4w3Mq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUXi3fAj8rgch73heFz1moF76F8QaukjnZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUXjv5vUZK3S2ZRkkj57aW8e49Bpa9acex") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUXNe69CjX5DFmaAzHxwY18KTXUKyidtT8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUxoebu8XkYqkNHkGfWB13MYUE2VTN5keC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUY3JeAyXy6pmGWb6SFNwHKd1vT659An25") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUY57jPSCK47EUeBcyZKxCGwvErLxgDMDY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUy6j79yVcyRDt2eorX5pwTVAvJCMMexTj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUy9L2bT7if7kxyu91Xeqe7ELUyc28w4RZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUYowzYa1mUe6XyCHZ8PXF7vnA8ehEYKmE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUyQ6soEmEX1CsccPrijSNQMZcUuQ4MR7e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUyS5vdbjojS89HisvLgxnDiXFqt91uiYX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUYxUk5t8jQajkiCgsfS9y2JKV4Tu81grP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUZ4tMf6igTUwHvCHWfZ82iNTXhN3rSpYy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUzCAy91KriZis7Z47c9Zoi4i6m1Vg3Ems") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUzhtctuBBWmq6ef34dRVuWVBGRYr3Njvi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AUzMsL6x6J1gUGXYWX14jdxphBYAdtNDFR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV14eghaL1tjehSZcVhSbpJoxL3Lhv8ugb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV1GUyQqcnHLohqJ4AeuLii4zon3mUEekB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV1SBxDiRztKU512jK95UuXy6rjhEBbTd1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV2EUmsuV3xwGcAw2J1G44PYHZTiUHJnZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV2fdvzRKwvfs1wpiTGGSVEx61BdL7vmVe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV2JgGDmd7tBkeuaoyGuuscS7H6yxWKfaf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV2X4zpQ8GG3pGiEb5swQfzgctAhLGXRf5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV37eZkBJx7D1b3aftjme7kza1H5SKRgTW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV3J6HSrmYj4Frh61sdUU2PRiMjBmTyA36") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV4c5oGn5nCr8chEhC7XWB2oJcV3szN5jD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV4GsxTA6ZUvVvbdSa3rttrJxwheGdNCrY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV4tCvQjaPRPCnRtmwgptqi6WsXGE5fqRT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV4Xcq2vGDABR2XUX6xFVeG5UcZNoSMFFi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV5ApaNyza7VLGn4shgrJaomFFBfkxj6dY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV5eH9pprbVS5EbJVo2J9fo6X5BZX2KY11") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV5fti3h9fmNEUPuTmZ4ZbzGn7ipNRjxZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV5ThdmUKjSjNQw9LWxHxZ3Uk7tMcyUu75") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV5w2GmfqCFTzk1E8SQcWWdrbgMFVyf8jr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV66987H7ZWAfAcBU6yFKEVo2KwSKf4QcK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV6bqUmNoe8j8C2twEHkJYUC2s2TxcdTgQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV6ELhWoLN1pYA6HTwnh6cPKDuz7aK18uW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV6GkdmvRgk9u93n5MiZbnVEcDpSz8EgJG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV6jhtVBA76QF2ZHouzg3bRuGPamLRnesQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV79qM1mK92dpa4c2fWqVJ45E7DurgbK2S") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV7FoNTDYBknS2UgvdS5B4gHtAv7aZjcSM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV7H5pzKJoUR8pQD45YTT8kFg8bbuvxTGY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV7WaxUhw5yk25zwQgrRaAQjLo99badtaX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV88UQmrxLbDy7KxLHPJrSgUrn89NAiqPd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV8qNNcCmpWkQ7eSNKYLw6M5ovDXwETwyW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV8Tgo33DPzCny5e8iKU5QmqrqpT6TMHJC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV91mmaqqAukUZ3Zcjbr7gpgCk31vvEzo9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AV9wm5P1bZU5Mvnsq8gDSnyGFUniVeP8bm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVaEEEV3Lr2pNCVwiEV1ar8AuNya13LzKz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVakdgQhFkypiiUmZ8optVAdwQWWPU2n5q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVaMy3Z58V6fZN9NbeSHmL53xGPUfKBqMF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVawbqq3BrBaunZBjPqNZ38sznwYBuPbj9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbdWoTJJ9gudwb1B9Lg72SR1NSyFzPUDa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbidq8WYKvP4PX3Kx1KoKuHFZR27SUzud") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVBizDB8cmRws4jiphJGABbjWj5piB1Sry") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbLDZzXPzVR5H1UKVkr6S9bPYtQ8w2smw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbPU1MiF1V1GJ4BdfzAkngHWmKDsXa4cA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVBuCdmgK5vAJCgUzEFLiRLEfzNpkuhQuC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbYxJU3ZnmtXi8Cvk4uVpn7jt99mKZgW2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVbZdp8NL81UGCP66veJWBY6BUFrS3c9Yw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVc6pBgUBnRzZBoNGnBJ4W2yPYkaoWwYbf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVC9ui8zUjuqeWQSdGfehS8G7hrECN3s37") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVccu9jMoqp8wgfGSwzoAtwVwkNRWyePMa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVcncAgMo9E8bo8StPncmgL6cXjnugrmGu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVCyH3EL2q8EcSfRzWqdKMKTBvpU4gRkjQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVDg6zYvGXUHM7PcUieNUgsiT6pDsogss6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVdJBoHK4YCkdJiUj6FsJfiezi66QP3XwX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVDLvFw75Yn6n99HbEv7Cvx74ubEZJDZ63") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVdoDthVcvrRdaKtm4Y1M8DCYXuLtdes85") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVDSknZJQ9kuD1krQJQYzshYXFHtapMoDe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVduACxZbKQDgf1ZvQErvYPFR3eoYKXDjj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVDxwKh89NzCmG8Qv6xXVR1a5jLFAFUbMV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVEepoNmdsSq6hNfuC1R34ryvQemheDWBv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVEUY5itLBC6TvwdkqMzRYdQxDHqpBP8WN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVeXLS9kCW4w2WcS6oKxTRky1cwcFsyyds") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVF7eiLRaX48VXuNWRzC9NmT2TCxMKuvoS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVfcNkMuQ7Z5ebGQCSjdngr9cYXoWkw5ZG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVfJw2VJNRW2E9YNXCwwaaM6LQPtMnosQQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVFkyvwqdMuJnTUygFJjKVBfoHMBTuKU81") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVFs4j1v8VbkvdBJSXx7kGW9htJohos2nm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVfXYbzhF1Wn4QA5EPR3UXUTvMoWB5HjUn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVFzXtYMDmmcUDLpaEEV7poCiyicqK3uqV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVGAttef6eL41ZMeu1fMMtDTQgWrkDhaBk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVgjun2WuVr8V8x2Nr9PVt6MEeJLfKiad8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVH2FJP6EF9SYZXtEekUPXSFehY6WwQHzR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVh6vPCghiq346RLqrEJWxXDR3hWMVGbVP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVhbAqrThVkugpQb9jzc7XmxzQEnVS5PJ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVHmFVDvodxngShqy5sjZ4Xwz2R1J3JJo2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVHP87ueAgRuHZwJ7ygeR61KNcb9zj9QNS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVhrhkzVcJzZCvTNEuDT8mzp2cRUEXhs4w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AViAAJWCV7tjk6fdYZguqcQfg4L8t173uY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVirQZzWfY1gwmqR9rZKuieuoZW9kAyeAH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJ6KUcJjnm39fmRwLD8gYnUPBLTxkoDBU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJ6WBRSVWfjtrFjF2qiBge88xVHVYs2hj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJ8dvekswxK27t8Y3Jb2GKPKRSVkvnyrk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVjAaVmaqQPQWRZn4cCiAwDEmAtQsxahJg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVjP15iAvZCnBdrN2fXaBwXPyGW7WQnTPp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJPusv9NLLN1VeDGjsssjgYZ1MNBAxiXW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVjQtUPXVG83qquHYJrKoTz5sL2WHVh5JP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJsWrqtkhnQfwBLeMp5hGf8VFbyJ7usgf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVjtAtMWHx8fDDSEvdM71sy2F8jPgSST5F") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVJwXkVVBgM2oTL6DXEEgqgdpk8E9voCwF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVKacSC5PFDi8u8CHv9qrkveXUXCSJNteo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVKGmsr4eqHMkbsj3bPnNgMjci8hN94VaU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVKLXzbG3Rf2TbuJVja7kbaXe2CaLHXTQe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVKmFL5E2mwXwffaMoQDhDrCG7TyJCgTms") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVKnWdekrBdnFUKykskNLxuLrHdhA7QLTu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVkv3Ej6qn9qPbctyU5PBJUtYpTgspfPWs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVLK4hNFkFamhUDEXUePnHefafCxLViz9L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVLm26GoAHdQEjXcSL85wuzdVHZXafXyXa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVmede9FEeUsmt3W8n7sDibhEkRQMYSBpY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVmjFAbNsa6wjWByUJ8Wap4Y4ivk8H6zqF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVMMN7CRa5qTTxMLueXyxLvAaD9vFX3idA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVmniGqTbaiTTA9V7moWpmfV3EVsuyQcBh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVMvtMsjWsNoquXDg4jPh2RZ6S4EtJyTrn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVMvXS9dwWXJjm4RGMfJcpPqmF7cUKDUJB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVmzYwR7s1ppC8pMFdv2UqZ3Sxfs52idxy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVn3QRGp23Px1e2eei8Jm5tfpzUXSLk9ha") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVnDFhJ9hyjnbdeG3tnaBMGRgNH7Jnx3LL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVnJ8usUtBcC2dkq4ifm362bxiGdiXcnhS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVNkL8ySDQspfwUR6CFKmscx3hMJYbE3fD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVnmw4tBc4CLLBPD5rc162MbGTGez6gATt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVNPFc1eQfG1M2X12cWsnpnshztwmusCV9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVNpjrcN2pj8XoeWFgzZEToZc3NZinR7Pa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVNTFmhkQgopXAWAyGz688BMN4SoTzrgwe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVofTpJcjZVr7K9VzQDR91rRUaoWoEjoU6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVoMFXyYWwJH33ZT3xMEHvkNbqk9yWnbu9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVPdV8BDgzQDhTPoKCgkHEgdM4sfBeQYpg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpFyZZdu45Td4mwxS4cPZm6Ess1HygsUG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpGn36orCi42W2mHMrsAPs3La1R77HXDJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpK8dnNk3rt7tAzah9gbrA5Rf2PP35BF7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpqKjs3ASq9q7hB5CJXZfFTHHVcGiN9rC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpSeDS4dV3UCTHC3aYqDyjwJGZYLaAdjm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVq1RdRox1NZaowWyoGu6AjnebMUD7FGrt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVq24DhkMk1pP2fcPheeoPfVS819wFFTqF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVq5zfYeLkH7egUXBPR3YAtJ75WnzQhK43") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVqAsN1Ggxnh8iSVyFywnSRkhHDqZbiBw3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVQUdvE83qfNxZTvWqmG842zofYHmAQzkE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRcd6XjC2HT72h2A6mqJTBV4Z3ioSVaj7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVrceFsjKL61e9GrM1Yjuy6KytYrsPuYCC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRhhYtrR4wpWkEw8X1xhGvRhPX7eqK51f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRNqi1tWd6QW3VKkYjn9V12s1CwE5otCJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRokSQLk8bgvPwUDbYt6p8xvZrSBAznoT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVrpbuMoFvf9XQJL8bTQEGbFYoP138XjdT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVrpnQnKp58hrkVmcTiUz1475HjTPeUynf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRPUqpUa9QioNxiL1saYFHx94dx17Hkra") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRtQ6ErQFHZZvsTSjVJ4CbJ1BzdkDUmaY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVRxf2qxDkSAF7ho5gjEzn6a5HyLb7EG3k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVS6822WdZ3DT35Vp66RPqNYtEXFKPBFFo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVsb96Mb7RCPW6EN5T8mAxzZWC7rSgh6S8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVSQ1bNZsAvuWwm3ZArR9z1VpSbmtJpprA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVswKjKpBHbqhQvkUNUgnKFvX8ysbk3nvy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVSWv56NZeW5pchhm6MuZyJwTxDyqwhp3N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVt15fH21QcDkpkf75pmmoebenjhXu8om2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVTBvMx5YajTtPgeWT9Be9j7kUadsoQ5rH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVTGZ9LirQZen1skN6qUi6ajwapqz5CKEe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVTqH3FMkj3UMHXMRahJqRPcDyMY4c5z8N") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVTS9McNsxD1ddih2Q45WUGHQmbKtYfCis") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVu3j8n5HfG6bS1yQx9LQ4tYknV4T6PbK2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVukUHB8UL4MHJrrhU3nUX6aJwaDpFag4f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVupWjJzM9LML9XzcMLEhyrJX7rpCqtaV2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVuSfPpMDzFbn3HNAEhRrYyLCzqNW1Rydw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVuTwsVmTuoi52YNLHR6zkADzemPZFgWFt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVuvQE5EzBnKhpnBRh4Gs85U79nCmH7375") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVuwYonWaiD1ZA2oLpcYMz37AG9b6eLqDV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVUxDBVadzHNDETe8MW3yAwLnk6m4ahfWM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVVhgD6JQhWJ1PTTc2hZqtg3TVocmeQxno") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVVwo5oTJj2gDEmgLHAGorE6agXyrUU1LK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVwAVqP6ji7TsBaXrZuA4YUraZ6WmrPqdh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVWdptxpZj3i51TdL1Znyut4oWBSWpucLa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVWEtsbWb1TbmcFMvubAju72eRnhdLxr77") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVWkTbjdRQqD8pbkYdLiFceDCB4eNqRWn8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVwom6z4Nu4HTVVwzPRiW91AaSGR7FDbDF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVXaora2ZrjaCzu48V2PhPTVhHEZY93ePa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVXH7ZP3FsPX9VywGwbSfxsiufnCCZBwKt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVY4mqajjL78AaudV3UiVZxbrxn7EXmhWw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVyQpAdx8R7TzxRd1sBgaYmQvBTUtH1rqb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVZaoRK81UC2QxXiUTk5ixziQRseLiJWdc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVZAXk4nNb1oCtj7N7Ldruop82XjRrXe9a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVzGPrsB3DmDNmqnenfw73Tw4F5amGwJu1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVzkDtu9pTpj83abhDFZnTpMEaHqhnsyTW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW2k2SkUMTDUvNgCYbgaZ5zXhpjfAw4wwh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW2oGuwn9a2rYD3TRWieyKxqa3mWP9Eu3r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW2VjumrBEUyG8JT1GjpBbd6Abir1T82P2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW3RFUVB8xRgC2VhzzYDrChYBdkW8HHX5z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW3swgPow4JC8QJQngCJyzVRWYyu8twyaa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4cMrp8YVNoVV76DK3XH6GnUUqoPSiMWW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4Dy2dZXvDhm4MPmQKYvziLqHdXHyyauM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4tNJV5xjPDzy3iKHkAZBoegZG1ARc6SP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4uQSYFQg13dBVzpqgRymkYTUyv3iCqAA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW4ZpTMGD7aMVj8ztGwA3nQHHxYL2Zj1DQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW55hmDN9wnyH5ztTa73iwg3BMV1g5BB3a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW57Xu9BmzkWpTCk5eQAeCXBHv9YVE7MBF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW5HubfLMvdvZTG9yLawerN5a2Pt7t6BXZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW6bB3s3GnJmf9G4RDXtTYSatGyohZKxYF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW6bZMmsdKQ4g5FgjjzCDFsC4LohcTEwyi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW6zeMNqYjN69rgRqvnPaWY5HgBavijxzE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW72CAmak6MTZLjYtHALqNYRWJNR1zmfU1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW781kNqCPJz8hsG8pYZvXZcamVyySjFjM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW7kkKTvixZhm8XEgvDZQkgsm6mWTnoxpp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW7vs86tjzx3bGd6Dno8kzKEAsJc2jEeLc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW831CYqEMZF1xLM88o15YS1ukSe6w6u8B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW8s8WUbPyxNAiV9M4YKyXAYHEXUgWuNW6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW8uC2DkeFymVJiGR2nVKjj4aw6NyTMrLt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW8uQWRgavkJP5BndMDetJBSrB6ujuQXUQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW8xSyHcHWZ4bGwSVQ5hQYejJf6CUbvpav") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW9bZ5AkSuswvCCHFBJJHXW3LZgi5ck7D5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW9FjMpcC19euzKnKHCnTEKrc91FSB66kT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AW9pm7xBngHL8AhRy6eB32q91BT5Q2JZjT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWannKuWjb4f4BK7AZaAHUXzMVfNiENaTW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWaQi9AxSX9v1XSDyhygWAYETgs4b4xU1i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWaXM3RmG4RgoYfPcA6umtH3ybY8DbYCmD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWBESnkx7ujDL3F7ZguJRQzBRzV7EGJ6G6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWbhdYecxRxvMbvYfHcogmH9cvmBf9FGZy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWBjF5375dx4qwPFvP7uSMVvjwkmeqSCj8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWbrH8xUqXYZMGMhB7YysMTCvFhHWvnxnT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWBuqnmLYQ4QCgz5xfjxFNsmRr5i5aXnpc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWByE1yqRSCnws2oDoxB6DwcznvjkU8qhC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWbYJ1bbQJRC3B8CbBZ62g5mcV7uYP8PCz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWCBpx4KkbNrVoytLJQ5KjCGK5pgCZu4dW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWcc2zmbCJ6S1RTX8HJotaD6WGiFe8uWaJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWCH3A3oDuKHD2MM6Un6LoMv52bwkpfkgg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWChP11HBFJxKT74drWiMAddBumAxfRaja") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWChQmxrHHLc81x2bmBBQPVSPkyp1dWjKo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWCHThzAq4Z4xWMBcAfP9W9q27hmCYeCVb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWCiFVwo4A6iRt282VsqdRkky7fJeQwHLw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWCth7HzfHgBuCZsU43BfKKNdRQ7vWHnF3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWcUHZHJnQeeozc1m5sCANrGMwB1HUZmcT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWdfCd81BhjsQ6u5HTKbhabkgGuqpNF8gC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWDGstph7rB9f52cC1SDiTqw1SYtT7TQkk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWDNsMCCrWGuPcS5XBTLG8cUvVXQwSUKax") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWDowQkLz9srAFDaf4yh3moF2Xeedgbb5R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWdYKmzNKBazrBZ9iHKB95L1i7dg642tTp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWecrxwNbskTSopQw91V5ybkVVHK6F4axP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWEDgxL4z5AHuMpGW6DyeBj2B7QbuYHywi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWeMGt4SMJAhA9Wi9oqunEYjUbAsMrUEuN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWEmHGXvWaQAm8RL5qxPFDrNZ598XjzZVX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWeNSFjGo75J8HrRpJYDY44AUSkcwpxCgS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWEnTHg6UFEFz6qa8nWDGxiNsdETEdfW9L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWEPTueuTYYPnqH2b5Je77xz34PkhXfsd3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWEyqgXYGjQQRH8doTFXM2ZguZgJpRhsKd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfgQMbdCeCQmG5eBBBxQtNMw7AToe9XAv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWFh7AJ9agfCKXGLKLNzWuPbrmF9aYWNvc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWFjbbsRTJoe1q5v6nCWnpk1qpP3bS3Q2X") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfMy4iuUu9xFmxguQ1RMXPxMrco8R3ys3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfNDWwNMg5RmpLFhLaSf7n7R4TzMFcMB8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWFoJ7taanmso5yNH1QTFsYnTFaJsHPvEs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfQVtysjwAmEtkeyFTwwkBCqwNygajmob") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfsyC5m1xxUQYhSuzKEktQJHRjqRnwUH1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWg1EhR5vaMJAbzyZCbzWcBox3FFoqnJ9V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWG3CRxLseZ36UeBe5JBgWuMd4NmhLDZi3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWGCiNAujoMshAQkBWS5MePkB3Kc5zT3FT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWGJu1hLa9oMUH5JWt3HzkFQvL8ZXKRgZa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWgLgWZtadjtxyJj6KcTiKDgyy2J5xpoWK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWgrqMu52mLLr7YvQDvS65h2uRYMsyKNzv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWHgrHZ7U57adUenXH8T8MYGS15MXGUbv1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWHhGXSCXSZf3ycRyQc1MGh12eQJV43UK9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWhPsDMhycUpo7PGtaJwzZhcLZWugiKaLf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWHsXocESnvVxrGGRcLxtViEzAxK4Fr8Q9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWhvY9mQwsnhaPa9rFBud6aEUi149Q1bPT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWi4pNVWMHk2Kxqg8wrAbvYTLBPUenxZhF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWi9saRKofuKD1PpwL2vV3fmTK7ta8niLB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWibiH9ZGZYEfpSY5auoys2UyZW3EDEL2w") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWiQKfj9jwWDj5wHahNz2hFT5jk6Movwin") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWJdNDpnpbitdfPVcCwx7ww9nAZyjGoeqF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWjECs4FBPEm8GHFBFq1N8GTe14tGTwWq1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWJKtNoDW7JHU9xEPBuL1VckbuVqV8PNFN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWjrmRM7rC6YVKkP34yM1z11Mt4ce6WpeX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWJts8NDjHdG2Mm2RZX3tv7kJmomwrgTDw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkcFBpFuT3zSnrFYg1waE1TUABHinNoTb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkd1LrJFK4CCT9XwSUjQqJLnRTQRonaub") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkdhoMX439EihqZqagwcQdH5iwNtRiCNk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkE3FSddDsShsKFawQ9aqo2KWe4QC2uW3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkP9sKnt4qWWP2vCbZsHwJ51AqQudFeLz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWkrLfpPg2oojZ3fEnhqZGQKtRxU6Ka6ie") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWLLPSW8jmqRLJ5NKsGRJeT3RKZ9mE6tAh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWm7Uejq7iKej9KMhW6r7Vcx1n4CqEcKfG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWM8BViaMFD39mBRgYQWHYvKNWfKPc7BdQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWMjAXGdG6znEcNA6Ksy6TrejCaD4s89jY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWMksR6nHc7J4hQA68jVsRKg24fRiFLLBm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWmnZCcKstGtdr7uksnKmsn79Trh2JQCw1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWmRAKfrnfBi8vHNcfGofaccjhJt4PJ2n7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWNQ7XMwLyHLvcYXfD6fE6ganddoXgbBTJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWnRfC41F6uzfGph8Ff1Vb6sJ2gtQYbKJL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWNt8oV8aG1fb4dSj7ViHRuyCPJWLCfaVL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWnTCHJhRJasp8sAiGqBuf7zW4rWgj7KFd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWNTnD3WM4tdHpgchLDKEVR3Hr14hWhQKZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWnU2fpnHwL47h9BJFTSv9izxKMEyPHTEu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWooLtMjGCTsyxcvmXkDwXrVB8eWwxg3D2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWotjn4uUmqF41Bre3vhYS2kWwQ491rTZG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWovtvWyxJN2YV55zrda6QzoaX8rqDDK2e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWozyQ5ta2spfHqBJFChA4wSp9qeg6njxP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWp88LEeTXAL4QUESWqVwWsihNT1zgYMzH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWpJmehLD2CtHy4bba9aPAp95pVy9GTMQP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWRJmToyYpGPs3igZvaCoSZW5zQxjQiCri") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWrpeNHiMmCGAJyL3KsZJ3o57zC9X8HRPc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWs7Y9MRqeDA71yV25isqf7GqrwcZrG2EN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWSGPvAfcXD3vZRb9m44gYjDzJWaCKDRbL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWSpSLzVFkfd5XcXgj6vJfJCe3Sr6pqbeX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWSrfm3H6Sv5fHSM91RBPNNZPaskkcTBBG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWSuWwmoeEMJ1ApXj26yu6hhV1sUBtfDWY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWsxXo9ci1cDtqwcxHL9YvVEQaNbb9DWEG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWSYg8hKkegtuZq4KTfUDRKzEkaV8y91CD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWT6FMNrRMkHDJGZcCxVKW4pzXGk26GwD8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWT9usjcJxGmsqoxoK9tovtMGP3Hfn3pz6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWTBrYQACrvS6CbwBdNbNKav14k551BhVd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWtfnPjWbHvk9Q8gDR3dibLuQaC5CAufTu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWTnM1j85jHuVcq69owh3zqzsrLkNmfGuE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWtuSpcYBde1mL6jG5dVxGY3vDBugYmnN1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWtwJuJHc94ERvEke7rSHhH6VPBKTwrR4a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWTY5jx84AacQTckNXZ2CwSswYM5g8hiUK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWu4RebZovCJyCdHeHEVyDEaW2hXBKvPF1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWUgK8itXS7qtrvxgQRQV3iCpKTTEr1HZb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWUK48k35UErWaC5QDRoFFzmRXKWhuwphd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWURBDiVNhYmWDjxjRsvAZESd4xuge6nJ6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWUYBV5rYRS6fcmuXtc5j6R4nR3fWRbtgs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWv8efvuyPwR8oSAeLUbrgogp5GnxiodhT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWv9cjsJb3YUPwNp256AKTEDWpKKUo3Wfw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWVDPuXEKhmQLHk7Mzm8emmr2C4Q7RowRv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWveFq3y3M23NdEPYP9SpjbZ3PDEpBYyS5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWvkvRXiebGq9rCh5FahtxMQdwv2zC3JPw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWvnhKTRfVU2gQ7iyE8h3RnPcb8q4B7A4u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWW1d4nnYqZPYtBQQWdH4ArjvGwEwf4PHp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWWbRqPvTmMoCjYLXLA2DJvbk8d3JkmyvE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWWc5M9D7QMEmhEgYKuEx2Ab6kNqsv3sLs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWWEgXqs22APrzQPEYV7LwQhLmbJ1gusqa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWwJ9LAAruZFFbHGgSW2q9SeCcAkA9t6op") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWWrfiGSohNWM8BhZWKFguTZxbXi4H4H91") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWwtxQAVdVvf1aUVLkE1GFyFkSgVUdGaLK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWXCK1TAC1jsZFGtKKz2CMq355QhoxYjF4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWXM14Zyhpfp5VsB2VLm9u5qxfmDQpB63K") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWXMtgGpcsVKjJfxNg8fhUtUFJ9Cd7rHUR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWxT9L81qPorvr1LjqasGhMp3oVvfVQJnq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWxvbCGgditCgX3VxB58ukHrKnxRrxU7CB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWy8ChJPkNTPxaReYVJn6Lhcgy7gAwXcEe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWydT442yGMcVmwRuTj65FgcZHLBo7WxAv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWyNtYJzshXGpNTyaDSjz5okRvt6aKR8iA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWYrdxmV1qLm2mQCXKSXgiQkMoJmFWNYt6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWytJ5Lzw9EPpachA5ErVbiNH1WRx45FMG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWYZgtfAAf6TsUZxjook4SVeFfyDkqWASV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWZ4482gdqqJwPmigaDyKomSYuDs37pe2r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWZmCa2yKgwxh5Px9pZXDgaEpnvAZUfSFo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWzNAiUMw2rx5L7q5JGffgrtEM1bUaAXb5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWZNm9m5M9aCRMNCKXqAkNJaEXnLRPeaL5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWzSikAV1QVYYPu2Y57hx8ogsGYDNzuw6r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AWzWLQMi1rJYUxYci7T1QLEbQVf48EbXhA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX1TZ2JuZB1Mrjy5ki1TiB71zWPrntdyzo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX1x7cA2wVwLNhkjBivAW2SjRHQ4GQ9Wap") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX2suTtMR5n1MxQk5DLmoNycLrCDWotKxJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX3ooDkp443UKJ8Q7sV8Yb75aKuR6r5WUg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX3pi678L4dBnSGPf7BuUjvDhJyPsHrp5e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX3uJFBHc5aEtgRLxQd5nr5e3YrAZB543y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX45HwzbvYstsT4uwxQXVeCXVHqtPUrRHQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX4ym9jQJuXHK87oT3aHgYMEfYRkNigUfe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX58Dp3xb1BV3P85p1TL3sqsFCNbHtDcoQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5AhR7wT2dstqbhrg49tzv8ZA9JGP6neF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5jMh1ndQW9j7D3cyGyhEfvMufeqDFVQM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5KhxuXvHTL6b4Qj6MpouLRydqTFoee9y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5r5UCKab9ta4zTjtyC9Mby6h2tHuavWC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5riSMerewmX8YaLXi68932Wmdj3r92fi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5sPW3acZeKrRUpJ4bAFXbxL4jXVv5DLS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5TPpaphMP5HbGuFThu6QCSQFkiPjdkT3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5Y81LUz8ctH4G9THQt4dchQ4hjxw9mYb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX5yU3nW9kmKJvRUnQQexgT5uaz9QiLbwa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX6B3uKwQKXDYLkiWpponoc6v4Vo4fKCfR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX6DSoH71qNEF2d2FqBQ2RB8VCxb5efRhe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX6ohsQqVfbeBCbYAqq9snFJZCCxWRTr5x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX6p6msZPJ1DsLrFMUdM4kMc7E1pR8BxgL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX6TUytMHekz2EzusoHNfxNBGd8iMBWTpU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX7aKa1CMB6wG2VJFiVoEhRHMCrbwGvcfQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX7Gdwpcz7CgQDqNvdLoWL32dcxLF6RXS1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX7sj4MT6gENsTis4tHeZTGCrMn8FQqNKc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX7ThoJtkqvL68KJD5DGeisW68pZ66pW4c") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX8ci9LiF3xnZ4GK6CAVZNFx1dkYGNgFgY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX8EiAzu4pL8dkM186gnybT4PRT5GYcwTA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX8GZ7YHiZ33TRzfpFgvt1ZKUkKaVHaA4T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX8J6AjJWJuvhGmj7dXNFxSHY9AXkxjGi2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX8qgYA48tLonaXbQCGEK1Q2JqmRRpmoEA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX9ntwAJsKyGVyyCxAf1Kokkwvna1dQNgR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AX9rPK142J4YdreEbXWp939fCX3xxzSTK8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXaAdUTVGkLk2tZYobKuj1ZtJpTZ7x5hLq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXacuMc1aB7AJmphuNxxUZKZZQcuQMkJnk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXAEfxF4EQGMUaQJXTGECL7gfTBdEJnMF6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXAeP3z25U1hgWhbM25LPi2JkHhzgUB57e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXaEW5V2rgwBGpFpEmNCt66znX3KPepRfq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXatXrhVnHXtKsi5spbSmGdV1Te1eisVV2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXB2o7efkb4bjCTCWZXN55rCr4rQdSsRSc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXbfm2MkHJLvTiwkMbQMWTpmQMVqdDkBBk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXbFTAcHZjLqNM1ZG6d6pNsqLwXNqEUHeF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXbGamQ1zuZ3XZV1oSmFSeeoNJet3SQFvM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXboZ2dXAsYtgFCCSHHsck9zVbf7YEireU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXc1sPhi98w7VegaFmuii4pY2iMUUPjymM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXc2txZS3BzvBKGsxoBxZxqHuE9fywa9fx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXC4RHhQLWq6gzbfUPZ5EmTm29TACexBPG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXcc85pkisr3wcmxycqRQw3oTpUDpH7CN4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXcjdCGvt8ZUcswDhTu2ohhMA6Y8VCiM68") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXCu6n2LtS98kHzszmhWtF3v8TWYv7jHfU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXcU9sLQMxoNaLYte8quBaCgzBsf17CKq2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXd8Q43G22Zqqw7dWbe1XLNgUNpzxQCNcz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXDB8pW8ifhyt8d24xxFixtrm3DBFDLAzX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXDCzJdvwkMwa3TaQACLcgDjzhoZsMeJbV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXdDUGRsaNEoD1MeKAwaUKTBxFr1NEgJzH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXdJz3zadEf8xFq3GzHmkYvYkTRpcyYK2k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXDuweinfXG57A6VT7ffpjd3STAw9q6FV3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXdUxd3wC1J22WcJcJfkoiji8GnvAx53S7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXdZojdvYYotv9UR4refZfoYBDcmu2BrT1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXe3YGL6EwyuwwQ9Yg36bMWhigEUR7aA76") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXE5xkhCV58j3THmv85d2mRBnhft6muzeZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEaGnDtrZMTisDbg4AABwjbJR92fQHtwT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEDfbAQ6pZp1NFByGTaub55D7FhLd3npt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEHWaa67ZLLpc4eKmPByqdJV71rk7WiQv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEkcdeW2Kn85YwTjHWwamNnUGhBvgHNAN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEPibQ9ZDCEmmM97DiTKtTLcpcuviStTr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXEQcNXPGQ51zwDwZL6niZzrVc6vXSy2pc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXeQdXeRLSkBkunyrBbjYVQLEA15GDSJvw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXFBQX4FA4F8XmFpMf1gEWcueDkGFFwHVP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXfegVaqqMh2QpvxjpMpwvbkojqd8apyXq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXfi69nKQ8ZMyrmMJvXpd7bUpsdmnYXuy3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXfN5iwLgHnbV126bvyjSomrVVLRp2t9SW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXfs6JK1b7aZffZeqJHQck2H2JSZJDH5xE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXGkzBZUshoPf5C9khEpNgeWSC35xwmgzQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXGr33xFtFSV4hh4tAmF5ED7ehF6ugbSsc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXGRmtr35yuxdMMWPDP6ii7XDSKvpCbqGq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXGWCmUHgLFWJmr3qYAyqbqaMLpRxpUFvf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXGYj33q5CkHLxs4mtpUDWEQrixreugPMG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXH49RpEmNT5Qrug8Kt4qDsyHvKp1r9F8Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXHJrpM3ZViaisv2izDpApjWRSajxhWg9n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXHNSoCxb1AzNMCTKM7ZgMMoQVJRCA3WB1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXhQvRLiG1z97ZoYsvMno9LrDNTek6xSTE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXHsj59mkLv4pwu8ULmzTL87oi1bxbdStF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXht4JWU6SF3fJaFvrEPPPqjHUykBV34BQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXHYuDJ6TYapVPARCfbvWo43RHyXqqtmor") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXi3zZKNwGcjNuDL5bXx9aDujyue99Lv4d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXj18NuibtkHSJRYFiK34veviNRjwu1EuQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjbBixW3BKnuXndDCV7JdbBiViFJc6nGe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjcMgab6rRkZHwj5YQzyqcFhxQk5aVbBY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjhAsMVc2u6RGLWi9AVgPyMSthL93PXYQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjNcSdw3YF4ykLccMGVkGgJguZjmhSmTY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjPjN3epBnETbQen6zvi5RkxkjNsVqhDX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXJWnt6XQxxU6N7oyrCDhwCxFWtdJZJ8EL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXjYKWMtcGa4xSVBmPmhyzxjMk7zChtCs5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXk1QnoKjjfqPkcWm4aoWGRfrAr7ceeuPE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXk3aWPMsosJR2Wk9FDEmWiMe7zBia6THC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXK43kZzGA4dBeWqbW9ioiMYPwGYnMwWPX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXK5TsUtvG1UfkQLmgEczG6Hjnbpiw1iiq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXKDgWkpQYqriLk4XxHwwFfmY73JVePMcr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXkF1MserBxd1vWYPsSHffuz46x8kcHgp8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXKfFaoPq45unhLGjsfWwMcLRS7tpPQdow") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXkFtZqVKnNiLmyeM82Webg6WU3atUJ8N6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXLcwh1ZrX2anfEVk3FoR7LotiKyXG7wVE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXLt1FVtTvbSiKmc31MMveiabrRC5ju7bS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXLuXQaRKQfxejBNjCVmR9EWaWhMfZv5oz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXM1w6MrBDVq4Q62iSFu1TKot4jdwgM9XX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXMCUMNKD3rjtmjAQM7Rnh6pVuSkEA6EqZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXMENSPU356s5GsQUpbwcxXjcidC5EfjA2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXmpWmcWCAUVTXnbRrbi6exNQM2zpQFr24") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXmxfXCELMyDuprQQ6rmPaW17VL5wztfMD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXNdW5XEVHp2ubshda1ZsEKCwCzHt6ftiw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXng4Jh2yyn5vxxxRDWgRmXTFkA9X678hS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXnKBvHNA87mTmhjVgMwhhapo5ULuKun16") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXnKo8YdNzinAL5MXKbTt9ZPygFeviAnVy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXNMS4Apj8MQX1qwhBzumsEjsj5Dse9Mhr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXNoY3BJzS6vJ9PKHJPCCpsF2jkTxeC2GH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXnTSghaM7HGpfw8od6rS9bSNhjTKT2rhP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXNxKsi2KjFTV38o1wX4Fwj79r136ZfE62") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXoDi2fPaqcX8z2oRe4sQdVv9bpmjMCi6p") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXoTMeSsPC1nPgLG66RFwvV6D1wMMReeQv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXoURvK7YSfiuG7XAcSa3vsF5mwBYKENSX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXoXqBPty5m6vT4LjzetH3AEQ7RwKUYtKb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXoxXSbTgESYGPgJxKTbYSirHqRjR7Ro8H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXp5QcK17Bu4PE9dRbqgjNFesQAYmCLeCf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXpfkJv9W9qvbPBuTLsLUtuDmNFAC5CUEV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXpVkwQADEUgwwtj8kp5HXBr7hZgPe1VYG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXqFHbAzVkCLcxaPXkr69qoxUq9Vc8Eu89") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXQHdBiS4E9cZtCcsBuuu5K9bhEK12aW5U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXQQxmAD1W61b1o6bgCidLZgNpW1JC714B") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXqrUnmr3FojmxFDPG67MhafRrr7Pr9CmP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXQw75S9Zy2UgqX5wV9ccZnC2x4KP4TC8m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXQx57ZoMxHsmVEEHLA52RgLjcxjPZQ4mZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXQYzd2aoeie4Yf3eoFgBgHKgKon6tbcgZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXr8H53JetbUPxKYcNfYgNtct2ZJRGdCn3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXRtLPhpBgu4oF5tnXpGePKftaNFSEVmEN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXrZzmE7bk8NfxFd7jnh65JvBNV6SfzHo2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXS3hRD1pX2tbPbQKgukzhyJbb5cMHP9ZY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXSGrNL8GzEsGHc9retZcHPJfi2QfrGeRS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXsjw7RCGhpE51ChDs8gurqHL8Fiaa3tQG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXSkMR8c9ocnGcHH3boaEjy9N8GrWXrhKg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXSSz8ae9pQiN6K2YxNJa9CA5pTkEEJnSA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXsurPoXjhWGiqkjemQyP4DRjNZA8SL8ku") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXSVkJhPVNZTdt2VZzg9Xdqa9GNEfN6zTE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXSXkZuusFkbL9pzvU1HWNtxUJreaTdv5t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXsYznTLRMjVyLwMWFkBWkF1se1xqB16C4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXTmnV8xDQLB5FHCNLuRdmddsmBZLnqQmJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXUhWvurLwAxNA4tK8kC2cTxB1xz5w5CNt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXUKPFDsV4xNhDw6Q8Ywo7zbEaiHan1bUL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXUQUcRHhZD7LJBHpSSFp6uDAzaAReib1Y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXUrRStMDfSkCZ8h6hBjVNeJvZSDPChtgP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXuScmZG7kzJr1b13Xa99ZthqjFN1NsAXy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXUuxBxoM97XgiXZc1VyGj1UyPBYcbwALs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXuWRzVUEgSH1qZUTQaP1zJcgK4BQpSPB4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXuXzj6RtJVRdmRgEjaLHvyKg94yh7vScM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXvBurfXECnfg4nb15CcgHyp9o29X2rs73") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXVDLmQfHb6iTykkHXF8caeSjCbZhEWs3m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXvfk5ymMfDy6n8iz1949Naxjh4sq1YoRA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXVkkg5NGmww9XabwDKGELjqNQm86iQTTj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXVT3RKCzaY8k8sCzJ5H1F6dw8Er2HAJWL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXW64tuxybvmvCDTY9EtYzdwjzHjJfUgd5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXw6nGUD1dvgjUnmHvdsaWh7Vi811gYPJf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXw8uDxNvgHhLREzLrLQ53rqfAanbEGexh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXwd6t4NHkJeLBUWdjzS13nYDPGXXmJLyX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXwEiJjCevjswTy19DhATLsLyLQUyR4kkZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXWLizpFomt7YRQ4rj95WVFwk3wkrrUDpB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXX3q2jy74iu5odi5rPfz5g81fbvE1gWCd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXxe4RWkHwTzZi37PtQVMZcgQHMZXEAHzX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXXKNQ6zYopYKmyAm6DkBwQjLeyrgCdQh9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXXVjBHfy1ncZji83L5jPQGQQi9ArFpXXf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXXYbQUQmXHJCJbeeVSzuMpKv2mBNQpsmL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXY2BUDLvnLYeKqSo1uugquGNaU7HGuVcE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXyfsqtDMhznPjuAfzWEqxYUmNdM8XGKro") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXYo4xYS2weQXZ82W2pawmukDAcBkD3k2v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXYoU1fswzJxt7SPkaE5f59mdtmwA1nAsU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXyQw5tfV5E22LpAcEomWzdrTHMsd7U6aY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXz5nKWmRWZBs4i7nKqY4LKh1z6iCop1kM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXZ8MXP2LyE7aLobb7x3fbjSh6a3YzsENg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXZex7EWuZhuZJQAVrHvieyRsoVGi1GSTo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXzhAwCJ7u4Pf5TVGU3CcN8EbMAHE4fvmv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXZJrdq5wycUfTWooZn5iUTkL7HzVW7pnE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXZoR3dgJy1NUXCsxyHvpG63AWtt35ZHYC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AXZY47Dr7HGzHqZP3Bxn57ctPqVKEeSjeU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY1LMMXA1vrJSKBWeW1D5Xm5XcMPwVtTFL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY1Ttha2rnSHjDpgDMft29vmNaVx44iL4T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY1vRjtjCsSEUoPoxkXYgjhA9JMP61fY21") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY2BXjz3oAcy6WN6T6e28izPZGWhoAUj7L") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY2omvXLjt4ahL9EXF3W6qynSF8ybTyuCw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY2Qz31UKDWBN62dBZGTBKpYGNXBw1FivT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY392EPz8BPASvBhuDP6tqDcmjpqNRMehr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY3ARuELWsEpgza8KWtYhDjJ7U9LV9t9f5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY3kesYxXnctekKf3BQnmoam7S5LC5J6aY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY3PasbGW3REQjKBBnVT1H6Upf58wTfoWz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY48jhdVFZDMn8TmrQ4JTC1ZSS14UJgHFk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY4fZ3L8oaSYwZ7pMz3Lwibhp14zvAcJC8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY4MJZS4X1c9yUN26w6pYWdkdSueptdSqM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY4v7JVuCCq3uHmycccz2LQe97pLmd1hyM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY5iymu2M9XVNsrXAtqJwtKagmRPT6mhTi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY5JUr3Ah2pVxtUyc32T8GqtAVKLNM1BsC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY62AqxRAKXpWuuPEZo9AmxspdAVvJAx6d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY6qBZrBQg6M1xvnYRmafGY6CyXKKHWuLH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY6Sby3o358ZUwhUWhSoSHbttT2H98j1oJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY6x7dLnUajj7u7VT73f7j71g1UbU3Bu1r") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY6X7pAfHHnf3e5N1aNRtsvaciJXNvxWzQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY7DSdJrNtp9VqU3vLd4EaqRVq6ms8aHKs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY8AJvJL41PxR1RSsEiE3ZEtwqrtxt1bde") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY8MK8DaCH3WyZnwukJNS6k8RnkNuVvzUT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY8RaxwaPhj9oEVRpVGWAuBiYTxyEX6jcz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY93KPFKH9pWLJNH7G4fRgC79fvVobDg8Z") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY95A433M9ewZ3YVbFxCeJFwiz8WALuDg6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY9EJqVygib6gPweo2mSspTcQXkFQ71QSp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYA4ZESw5ed7JBnX99aRNC1ubXCpSrQkfp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYABt79gxr3WPgFrwnEkSkCYYmPCxoahq4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYaCkBQeU2Z2KhDZxKWfmS1u4L4PtU45H3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYaCVDGKZLkpdWzc78KzSx55BXWvNNym8n") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYAjExJwyt83RnUG1b8AyTBFFtaWGxtgLn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYAMhtK2MLsuJ5nUSNfVzSJtJmv272WZeb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYaxgX2wWaiEd3v4G2x5cfqh17aKoaqhBa") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYb59bpbSsSEbAt2g9W6BeAzvhndvF9f8m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYBDFZCMkmiPN3bdWpg6GbsMjNUt3Y5bgT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYBEucmAjWgwySNNhKtzfWUbhBDi1v79Au") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYbnpXb9hifr2S4RozECF4vVC3CFKyLk2v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYBS1zgrx7V11AKyjU4RgbYVmLEAYK1h4h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYCjRRi2LLm493JcvFryw4qTcG9MBgdHac") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYcjvjUikQ3QNRAjpct5LB2rGNbmeehbB2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYCwXnpYdwbYnbwX7qnjkxfD5dLLWZex2C") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYd3ZcTQ2bSbuLfLYJKuRKJ1QuFNAAvNGD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYd5vhftZQUdfdZQRmFtc2ZvBrFrEwbzbJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYD9BrsZyRBqxZDjmuqqZbxdP5JDXJUJXR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYDkcqaDRVa6bwgJQpJnkm4eM7hNWZBEaH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYDL86Rp4is42bjhGRFtuhv9x7wLVvZrr6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYdPGorvbaXh9CiYuzptULi9UKYyRdPsHh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYdrzSxM5N8YKbeabR8dM5ggDm97vWFj2f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYDvDbUmGnqpE98ALvQ3ZKWDaM4WHaT7Zm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYE5sZ5xzNv2B3w8jZ281H1becpjTUU71v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYe6dz8Eo7RLLHCu8ZyBZMx99mV4qE49PX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYeEv8wG81T1yvtQhk99xg6DSrp9F6ymET") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYEGDR6wyykQ4suteYM98VgMGHbJBZRciP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYEH753qwVUQJwiwAot5NPby3aJyevCLek") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYetvNebLyv71k3NjCvS1qUkPSfyB3XgDV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYF5mEkcL8V9rxCoq8npWdBW5nxAfeSyqG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYF8MyfZPnQncXD5XGmGaXM41RzX9Gx9ee") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYfBJE6NAUjdkhjHStguWCPqbTj5Xa8RD4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYfidVEBT6oycBPN8oWTe7JmjVKmANrRL2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYFjwB68LNji51sP4J3pHWJy4YfxLWypKk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYfU2nokmEAPpMKXss7unGRjUVvuGEMFSb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYg1nRni13rfNcaaHgQBovgr9VinjKgeKs") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYGArCK3kdwittku6vuP4WNcH3TryzdbJw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYgEH26R1TZz1aqPhdZSoh7eyphyksaf3W") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYgNLpCorJYTvyU7WhN8c9QT9bRfVb1xZr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYGtC6TwUgfpaH7QDLwKVA8esiQDa4pE1e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYGwTtjDDb5DTSxNLnvoNQobatNMhiPM9U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYGX6RJRC8gFz7hRZseKarGksHCZoSAF7E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYh9MLm9GajVL3EakQdyNmchA1DsXkrRbM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYhHX4KD8NPdjC1v9DzY3WVf814LZRkeYo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYhmWAfGiJxpGN3CJFJTVsiCh3aLUPGrpc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYhQCTQLbLsA2Nro28GAcFWgfF61DW7Hn1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYhtjF3o3j6yBMXBMenBAXaiY3hG5GtvY6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYHv666oPUyVC7RjWHS6UR5TWUHYeU47Su") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYHyywqMtdKK5yrfVJ8SCvPmeXS3sAkMVA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYiBq5PMsNPkShrKGZgYpy7qvuZq9NFDrz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYiJcvFokaQjcaHuYsjJqxfGb8HM5nYNbk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYiQu8emd7q4wHWhitgaH6BU8xTxbSz3r5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYiTxUdSboYm7MHgCiDxGhQYdKEWL7szUh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYJ7MRrfjLbzoYY5uRsMSSEWVBwxfoNEaU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYjbGmVWj8ApxuRrE9cF3R3K9R2DggadFR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYJioeGKyqomuoY1UiSwgiNndZZjkai2bN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYJkGMCF3cUNykKLYBkqxstaNAUaxhwsYt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYJoPi6uDvAaTWks41SDYJLM6LrFpDu1ZX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYjx9jZyFbRFjgAiFsodFu8E2DJK73QN5a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYjZkpotdjtX5EYxMq2XjTzbSYBpxNTY92") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYkQEPM5Qz4C5RjxX23Z9VNiwXPvN4DNRJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYkT248hhhbFwDRjwPavryXjaGVKknpzBW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYkTJfhRk8dGV3HEFN2rP5RUXQuJ8bSnsW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYKxArkpjxdk8kbdmgYV12Jh3ihzjyr2iV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYL3Kha7QYY37ckpuSP8oDKFNbWrLoWfQV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYM2qVsnN2ma9gVonfPGFJmM8re5H4TbM2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYM7F5S3qkgohLvw8J2bn5vvtjc7Aj13KQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYMhqQQk4edMfjjpF8wMpAXUw3GeFqMEn7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYMHx976Ay4JZNjpTLwx241v6PLzHiA671") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYMJKPwkMR4bjF4oing7xuwtMXtD8cHNcG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYMqfjMYRUfCGaaBX1SFA8XemVTceXZCdf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYmWQYj3iJmM23tcjRpvmvnshfdpfKEnQc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYMXdwD4tFxQnazvPPRjLKamAfYUGny8yi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYmy5h8CFDQefdVjR7WZ3nNaxjVMqs4dDL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYN84Fvb65auSCxyp9b8rwsJPWkRnRW8A8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYNaupMtBmeroy5nz7cmgsL7b1zEQumBmN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYnkTTap9iW91zEZkCbBwYr5ePkMmR1RbF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYnq1hGFXnpyDgN7pHbTZc5EareqgAAqNZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYnRsF3HbVdMmTAwcyuzdf48fg5iGtTUxh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYo8Zdyn9mt3CxLZn5pEVvY9HiVmnmjGLH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYoaJBriDihzSzahXQiQTLciW1h1kyHUcC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYoehmhVdxikcu2CcVSzXDAFB5zexP3VJj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYofgcLep6AYdDXgxG7uDXLi9bB5nnWbVq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYoVZxZbTHPPApSMH46aNZADkQ9KFdDcz6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYP6WXPyFTsqCvjTJTe8yNYcWxwBu51t3q") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYp9RWiAGDE5gFEa65Wh2yERE4pismLRPc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYpcjm21LEbhoGqzmsExawqirQV4xMDgdf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYPFmE7CzvuW7iaPCosU2utEKPojgaAedZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYpn68Ju55RWM3FTSfxsaPRUBxebDvQmYt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYPqhkdwaqSuaE6gAJZbRQrJ9ps3PRCW9U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYqBNg9DNMd1hMpzGHAgM9XN2k673dCB24") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYQjanyBqNx7EckJXH6Rxi2qASzKg6NRcc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYqR5uT17a6uXQETmczPJmH5A1VMRxBiYv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYrBFTiifEXkuvpGaoMGf5mxthDg5vWGCj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYRDpofg5fjUkMhG8p9PevMELeRjru2hoV") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYrwHyVpbJppL271dR2onLGm8GzcCQKpbZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYS6RK9xdX866DAJdyBdxWuoDxwJBaUsxS") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYsrFWy9Q45tRkRnbYSAMy2FeLJTuNYJ2E") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYSrM87vAc32UKWWPyt4UA6k41Z9u7bVoJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYsrPspDqpAb7G4urbt5TgADbr5Tun7goh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYsshbTa7RLMHfUsNh7vaULWdDvhVDLWTP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYsunvoRn55yhEQ9sZE3uBr4pYaKgjeavU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYszSGjvxeiVUuGw6KsKMV6ghiJqPMX1mo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYtdhzEDnhVvX9wMVXrCM8HPgoUFRiGEfk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYtV3JUGwQP3VTmua26QHhmYCcfqrG5g6a") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYTxmUXo9kD9J1RuHw3vqQPfNkfi7sjrFv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYTXozuNAeL5fRaujK1b6cnacNuauW3aMp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYU12SxANoc7vP4fSzm5ZfpfVMmH6i3Efn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYUCRefK311nK8XNYYdcdR7SwVCC8KrZn9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYURHqA5e8M6Wx1apgf1wkPNQRFiZG3dXy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYUrPj6viJCeziExpMFbg2zX9GUw619WTB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYUsKdRXhJcuwBHjuznSXy5LrcJymMXGN8") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYuSuTpU9stzPmAU4w8w1af7LDq5CVipVx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYuxFE3t4N6AoCEgc9xh8hBoMWhWo946vq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYUXfwZHhXeQRfQjswN9pZ2JWDv6QxTSbW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYV1U6148Qf1kotmr5A3LYpHuNs7UbfiTC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYv7NzF9iyGz3756KfGUknEthjF2tkNcjr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYVLsGaE5iSimJma3iDY2EaDeTw9EhbqXb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYvNxsSazG9A8KnZHRe1dA2C96yWHv3Wmx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYVVZYzoPJvALum2iSDDTKx3uUdhQdiEQe") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYw7ziYXFfV2UNFv1CrmLqSkzs5GMEd4HA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYwxH6JuokSgg3XWSnaKVJxYRdMw3Q4GcC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYX7TaPhUqZmQHxy8aQ6gj2synXHunHw1f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYxkgJwkJVMn2bSq1CaqpLbc8gmeynrHfF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYxmNuGZwxerso75qwHB1HTUVe3JQ1u36f") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYXRUVvDcMcNp6Q6Xi3uRiVE1P4jqFAMGb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYXvhVS7kPv9yVfxaBHttqCKznf5Z69Za6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYY2Wozd8RbFdepBVN2RwZB9a6qA8Ws4VQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYY6W8soVAHNeGoWnSDKC27PA9svX1F4LM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYyHqJieJp4Gdhm9RwMYBgM3JN4VDEw7LP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYZB12PVxkbnD9K4xV5E68SQD5VTvsAcU5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYZefN6AZfDQZHQmYd5kS5w831iVrzRq94") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYzLcbAemSF5mU5decLgBDjfQur8FW3FTT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYzmoZfyGZwddyiB3JmEwExxT71yBkiFpH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYZpshAPdZxxc5QUeZdiv6MGt4syvP6f6y") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYzZ3MuMUqXLhjjvFjy2CG37p6yCAkYgfo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ1B2d8iM99ho5CtdoD7ypXpYbuvKmRRGB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ1Fmnx8zxMj67MXPa5AqGwprMiY95sj4V") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ1JmsiCJ8SwTEnEgTH2Pqwf1HhD1Cj2j3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ1vkwBu9X8KR9pby8yGe8ghBLa1tY4PW6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ2GvzzTCuGMeZwW5AMD2xB8E4b3WXiYk4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ2iPz1ajiVpb8Sf61SqKnHqXqSoTqzpoK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ2py2Poiv4dAnhAEQ3Ubgi9v6YnUcURjc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ2TpNNf7cKdHJgTeYeYzhZ63RsoxTbnAq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ3xFtvbfL2K9LeGBsLtdr7y25DveoN9JR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ4h1KshaxaDrbRAdFi7RyjVkz4Epyx1Ev") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ4JjNbehGDLGWN4QGaxSF1tdUSySQzv82") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ4kTi7YZX7CjWPY34465gseWiugA3fz3i") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ4KyHKeEXvPe5BeQ9yfUgNZYN8yifwERx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ4uAULmARpZoGBfswe8DqayE7xrRTttoM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ5EgQ2GnhjLmVsZaz9MyDqK1rzU2irL5G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ5jEKpnVH6dtcUyCGBLhHd45sHaJ3DcDX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ5URAgRHtMhhsDX2fF5yZ7zXKGP8sbySq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ6dND9grQBgBosXxkUGgQuvdDn7C4Bjct") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ6oC7K6AvYbUdqGUg4B7tmD2wcKM8z8Cn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ7iBTBMMKKi2LMtbHRDayRodUnSRYBEBc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ7xeUujLwFjGBykfGsHfpgW8ZzuWaMiVp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ81GwHuKoHphtK56YTv5z37arSmXX2kSq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ88nwpH8aCSk81QUQQht3VzBTg7Z6UM2T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ8pfpYpG8NutB5v8jg2g592sKDBrjQzdX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ8PJNBB3fDnrvkJGPcPs7PutXztca8Ukx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ9aHBMPHPKp7jiucsWUFwT2vf1Qer7ew3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ9J7HSzJuZcK7Na79rYowMHxYoAW3nXdk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ9PRnv1doCrqBAhFvAFKcjFirSz7eDKsp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZ9ySv9hm1SnQPAnYQLEmKSiv618vCAQD5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZAfUGS5W5jCtVLajikGQdXQbxQFQruSBB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZaGtt3oEiCACT1QHea9sjmTtFHSoJkuFU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZazQBateDC5e5TNtWFLqkSjkj7X2vc95G") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZB1PiC6S3uJoFtf3HsbRj3XsMRWfqLG5h") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZb3jcJ5bWQznoG6FouhbfeH971NEzTHai") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZB61wiaQbke2t8sVFovLYWJLS4UNu2CAz") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZbaiuxtFZtmmFJViuCuf4EmNMpviZ8tZq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZBcKJ147unzggdM3xM7QHYnMsDnai3wbX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZBLNdxsPSyK2qtAD4BJYYugwR7D4dVRQN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZBTYWNAViLQpWSU4DcuDc8Rrb1663BNJu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZC6kkeQsMwgKCyyb3wK1HdbnEeZDvhtJn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZcbBkNVR2R8rVD1pARVP2pDrhsunoyRUp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZCGwLvLqwzgrtNNqufDXTz7WnWkKJzZJf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZCW5BoB8bpiKpCWEQXbUCLe5aEZcHcEYD") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZd87Qp3LsGWEY31VJAzfneNM5jh7XGPSG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDAHHEB4t3SoBnTRVPs8nDdpmvTXxuabC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDCcsD8n3gm6UXCAsGfjGTJ3TZe6Pod1H") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDdSv8jcMBtukec7MCSqkX1qKSY7rfL1e") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDn4BBoihfRTPWA7hKAFhmQP3wbZ9asHB") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDSYqn2JBmpeuWscmFwScNTcjLFxwApEk") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZDXkB9UrBzfvAhJVapN3LVmYmZQf6Lf3t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZEBEW8wuctmkCXrm8sDs3szBDi1SCNBjY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZeeune4Rx4QSRbiff2wcxBib2JQQFSfRo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZeiCVe4QyWQqoeFL86DJyfStB1oana9jA") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZEJUcjKn9rhvJefh23nu8mCJUyVenueQy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZEKioJ7MTUgzs4TAbx2xWanyVLKa6e97m") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZENfhQqNY8oxiWQHwgfjfGt6Dj2d14852") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZeP7JY8aXWF9UW4ZSSKef5ELjnqVFrHuE") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZErBSn795Jth9kqDuwYfGmLAFRTMAoJks") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZeRyUdHxMkSEwfp86WieJUvuohXWcPHGb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZEsVPTkE6TeMCkBx1rgbLfC1jZ5vkzKRn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZFAmw2j1PYM6WvFgK5teQpgUsxhWN3uFc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZFBvCpnk3Um4nECMDVS4g7TRd7nMpQVAc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZfBYyBpcE1tS2kve8o5Jav7pinTmoaEUY") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZffkWfn8eGVKm1ZFwjQLzGtGT8cwC9nwC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZFGAwXyMGsK3eojaxAPjQhhhVfEdCeTcq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZFmgLFNmXxBm1ihAZv6Q7Qkt6hjJXPEez") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZfru1uSwuMPN9XbaPCvqJkQExmTHRCTfq") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZfVBgcyKnkuayjjaQ2ezj7yUgMz3G8gph") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZgfaZe6yqxjahn1JN94dwgY4qZ8FAexVb") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZGvT66NcExhDKCVAx8jdkKQiATPprwvoP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZhmM13BoZh4VQsNxs4Mj7g55YoQFRMKLi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZHoEDtbsiVwptiTcehUfSo8L5NUUcsFLr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZhofFgChXWwCuBrcZhpK7Zvywaz97iQ9g") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZi15KeYYiW3ohMEvzk11YHFD6Qr6GY3Ao") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZiSQxYAt9iHqs1qLirRnKrocHWcxJbJnJ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZJ2mRxeHxau6RjPLmc3mDmY6PsPKQKFkd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZJvnUpASXCZsuQMFmAUVS3Akb9DCHePEc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZK5os2FcKiJiiQGG2ss2i37VmgTaazrdL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkcxmpyQtZBhhWBcbUmsPdPTYxoy6WVkQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkdqB2ZyLEyEFH8Rtzncj5QhJ1U2YhCZH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkjANwk52hyN69AJ1omwFt8JsJcjm6Zon") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkQY57qfqurhXZAyHw4wFA55GxKbVKUiX") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZKSdQGeeJkjfCvkrwvGH3oz4EK4iCapQg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZktshVABoCyNwRak1a2kntMtTK9jBGon4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkw54RGGUMxJE7DwvEXitH6ZoPojBUKnd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZkWJBCsrzBXHNxnPWM4x3tuWdTvjCvG2R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZLaR6x4HW1ZT2CM7LSiQjZEa3AzJsCuvn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZLg9n3B4fWkEy6wMkWk3cJ8nN8VTBo4vG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZLpvGMeEyBu4J4Pbh9BKq3gumxNz65225") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZLRdqFzzcRa5L5TKDkNJT6r3SDogLLnEL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZLtsHgWDFKT4ff3SQS4NPAQqejFjw5rtQ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZm3irsPqpcxY7M6kmAf7V2ssZr4QS5eUL") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZMRwMPJXPSG6d7eQi8XJrjjj8PRMVGZhm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZMsbJGHBoxkSskM9cTXDLAgabFEMX1RAT") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZmWTmyno72K7CMgBYnX4PtQisG15daNfN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZNF3WU8AkGj38JXjd4rhpYXTRQ7HZM4ap") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZnN7iftyaRUn2LNyeG6eUvpTCFokpZRL2") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZnnKijmhUmZvLuJTLuCfbrWvJT6QwKqXH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZnVcL8KjBvLg1fD3UeDz4di57MDnqqQJ9") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZnzLBgbMnoijcGxA6HQkWhQ5ZFgHZ61cM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZoCnsuobJzU1QzWdDt2ACdkjinkz72uvf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZogzkFUCfq5ManA1pzxwn2YdQnDedL2yj") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZpbCRFbjSZVntSgKZSJggQiT41sRtvtfc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZpjLjdBVg76SRLCuCGooZ6PhfV7HQvDW3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZpmSzaLw9EXV4BwPmH6mFkrfv8gPnjPv4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZPPDHsfNs3M3a4w6rpuapP8N6cGoCp2rh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZQ2kAPT8HzC9B7uHfBS4A2dT7L7f8nRiU") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZQay9cR9m21Mpv8QuQQkiPtg1byFgTbSy") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZqK6P4uBkUh6WEn9fshdaoZoLHmp9c1at") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZqsQ4yVcg2PxNKc68NSwUg2cPpW9HHgpR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZR5wE452yTkkb8J4RUWXUHMkhgPCxsjVx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZrCwJJkskAZtihegoTA17cgXW2VmwBNXw") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZrfRsScwZqJa715RCofLZyYhfSw9jYMPF") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZriC13soRMHozJksVz5kSGssVmX4v4CbZ") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZs4XMZiP1g8CThzArKto5NtTPU5fAXPWN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZs6aZq8WEURbb8dAPdLC9THcvyyKRDDU6") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZsE7Eih7T5mwPJ5eAAJKh8PV4xTUsyxFt") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZsuHL27rh4HCQYABgoB82iB1EJjFVo6ie") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZSxNgY87CjkMadbW56z6nZGxf5Sd6w6rn") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZTFXmmDcqZjj3WNy2AgqSehHm4S9R2qFN") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZTHY1dPR63mmUvqF7LG2hgX2oSgRkSgL3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZTiTddxe3u3vuwW9a9VZznJQAgiK7KqCC") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZtomvjQK9VgmMRcnSnbDYntCgMiGP6Q9x") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZtRSfF5KRgBLArajca3AfrLUYBFwy233u") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZTUQncAppSYi76g1UunnWyKjdXcjsCT5T") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZtXqKsXhUrpLnPaWkTCg8kGAb6LcKUVCG") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZTYKFkY3pJZiDQh7dFAfB9WntCfNEadVP") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZU6aU44XacnMArPXrCSrmFdd8X7VeZzDf") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZUfHVjf1LRtYEfKQUfJe8iCCKfbJSHcL3") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZUSa8dqxQ6mPqv6CudTSuzz2FyrVwDX4J") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZusyEotjv4zzU4XUqbxbBYwULMtDuWJvo") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZUUECmVkw6L13yYv8KRhXafevFgzAtqCx") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZV589uNciPqCoxa7gyAMQDHcR7NjVYNPg") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZVDrh1RNDNSh4ps1P2pEiF4rhwtN8npgR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZvFX29D99iJtDyk73tuNPWMgq7x98J9F1") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZVJ36bcLiJJVZQY9eRjYU93Y9dxww8nYi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZVPtfTA2JEHWSiUduj5aPwyWtsL7nS2eW") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZvUr2K8u9Yzap3qaHRchhiDd81tytu2sM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZVVeNufPtaeRebjyWJfNnAit5ZbTBgd77") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZvxJNF1Lxkj1vEMijkL32KzsFiTkjB3yv") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZVZF5iKP9JJYu5EXpEHDjkfSjRfSUCqF4") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZW5jKmYWYh2NCUpy8taskqqtnGCd77RvH") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZW6G654QwAQ4eDSwduamCgQrxUpkzW2pM") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZW7F5CNSbVLnEpKoZWhZNNWLZttvsc1j7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZWbeLFW3QbeFJs7RvryJqs8B5QJ2AbWnr") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZWi8rWxcUhZtwvQeUoo7tHUqDnGiabEGp") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZwjbUHqT5AYF5MeiRBcdHs48Dszv53xWi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZWPPfTdpLURxxpTkPjE5WLaeD5Z6yqBMu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZx6oB1vJjRd1BZJqbH3NuVoriVH5A4YDm") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZx9WLQYSjHBAzoLqz5gf5trRrBPvmUH3R") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZxazqYjgWurtxVTVjY3KdbhDAQmm5Bw5t") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZXGK4g7r3cS6UzmZjEVzQfju8aizGi38U") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZxraLEmwkZW2anr2YjzMWhnfXkZ7MrNeu") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZxrBXiYiMQWGahdb96w1RksvSn9gpN3dh") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZXZSYBJydg7RH1rB4ptasCxmftEZUvB96") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZxZT7mnAxUtWHjq4yKpkRSFeL2YToqLQ5") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZYcZAjLKLdc3LbiDByvPacsuHjMS7koro") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZydRHm5y4Rz1wRMAHEGvUbGAYqdXKDc3v") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZyFmSyH5RBGb9VWfSPbTvTsZMcrGTcBvi") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZyHaP1cLJsCijpfNLeX5s4F7D5cycLXNK") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZz8sPSS7GZ2VeFAKuzLZ7HZZ4xjtNeFdd") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZZDz8rkxeFxBHwX3jLrvXzaQ2HED9t5sR") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZZsyDrUdVDRgqeozn5XUSCzPVxwNqAF6d") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZZWEdsdBwLEYFhCqobwwrVi2r4dKHWmNc") == 0 ||
				strcmp(addressSource.ToString().c_str(), "AZZWYMqHzwPynpm46bEFRLMi8cGm25WYDa") == 0) {
					return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-perDevTeam");
					}
		}

        if (vInOutPoints.count(txin.prevout))
            return state.DoS(100, error("CheckTransaction() : duplicate inputs"),
                REJECT_INVALID, "bad-txns-inputs-duplicate");
        vInOutPoints.insert(txin.prevout);
    }

    if (tx.IsCoinBase()) {
        if (tx.vin[0].scriptSig.size() < 2 || tx.vin[0].scriptSig.size() > 150)
            return state.DoS(100, error("CheckTransaction() : coinbase script size=%d", tx.vin[0].scriptSig.size()),
                REJECT_INVALID, "bad-cb-length");
    } else {
        BOOST_FOREACH (const CTxIn& txin, tx.vin)
            if (txin.prevout.IsNull())
                return state.DoS(10, error("CheckTransaction() : prevout is null"),
                    REJECT_INVALID, "bad-txns-prevout-null");
    }

    return true;
}

bool CheckFinalTx(const CTransaction& tx, int flags)
{
    AssertLockHeld(cs_main);

    // By convention a negative value for flags indicates that the
    // current network-enforced consensus rules should be used. In
    // a future soft-fork scenario that would mean checking which
    // rules would be enforced for the next block and setting the
    // appropriate flags. At the present time no soft-forks are
    // scheduled, so no flags are set.
    flags = std::max(flags, 0);

    // CheckFinalTx() uses chainActive.Height()+1 to evaluate
    // nLockTime because when IsFinalTx() is called within
    // CBlock::AcceptBlock(), the height of the block *being*
    // evaluated is what is used. Thus if we want to know if a
    // transaction can be part of the *next* block, we need to call
    // IsFinalTx() with one more than chainActive.Height().
    const int nBlockHeight = chainActive.Height() + 1;

    // BIP113 will require that time-locked transactions have nLockTime set to
    // less than the median time of the previous block they're contained in.
    // When the next block is created its previous block will be the current
    // chain tip, so we use that to calculate the median time passed to
    // IsFinalTx() if LOCKTIME_MEDIAN_TIME_PAST is set.
    const int64_t nBlockTime = (flags & LOCKTIME_MEDIAN_TIME_PAST) ? chainActive.Tip()->GetMedianTimePast() : GetAdjustedTime();

    return IsFinalTx(tx, nBlockHeight, nBlockTime);
}

CAmount GetMinRelayFee(const CTransaction& tx, unsigned int nBytes, bool fAllowFree)
{
    {
        LOCK(mempool.cs);
        uint256 hash = tx.GetHash();
        double dPriorityDelta = 0;
        CAmount nFeeDelta = 0;
        mempool.ApplyDeltas(hash, dPriorityDelta, nFeeDelta);
        if (dPriorityDelta > 0 || nFeeDelta > 0)
            return 0;
    }

    CAmount nMinFee = ::minRelayTxFee.GetFee(nBytes);

    if (fAllowFree) {
        // There is a free transaction area in blocks created by most miners,
        // * If we are relaying we allow transactions up to DEFAULT_BLOCK_PRIORITY_SIZE - 1000
        //   to be considered to fall into this category. We don't want to encourage sending
        //   multiple transactions instead of one big transaction to avoid fees.
        if (nBytes < (DEFAULT_BLOCK_PRIORITY_SIZE - 1000))
            nMinFee = 0;
    }

    if (!MoneyRange(nMinFee))
        nMinFee = Params().MaxMoneyOut();
    return nMinFee;
}


bool AcceptToMemoryPool(CTxMemPool& pool, CValidationState& state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee, bool ignoreFees)
{
    AssertLockHeld(cs_main);
    if (pfMissingInputs)
        *pfMissingInputs = false;

    if (!CheckTransaction(tx, state))
        return error("AcceptToMemoryPool: : CheckTransaction failed");

    // Coinbase is only valid in a block, not as a loose transaction
    if (tx.IsCoinBase())
        return state.DoS(100, error("AcceptToMemoryPool: : coinbase as individual tx"),
            REJECT_INVALID, "coinbase");

    //Coinstake is also only valid in a block, not as a loose transaction
    if (tx.IsCoinStake())
        return state.DoS(100, error("AcceptToMemoryPool: coinstake as individual tx"),
            REJECT_INVALID, "coinstake");

    // Rather not work on nonstandard transactions (unless -testnet/-regtest)
    string reason;
    if (Params().RequireStandard() && !IsStandardTx(tx, reason))
        return state.DoS(0,
            error("AcceptToMemoryPool : nonstandard transaction: %s", reason),
            REJECT_NONSTANDARD, reason);

    // is it already in the memory pool?
    uint256 hash = tx.GetHash();
    if (pool.exists(hash))
        return false;

    // ----------- swiftTX transaction scanning -----------

    BOOST_FOREACH (const CTxIn& in, tx.vin) {
        if (mapLockedInputs.count(in.prevout)) {
            if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                return state.DoS(0,
                    error("AcceptToMemoryPool : conflicts with existing transaction lock: %s", reason),
                    REJECT_INVALID, "tx-lock-conflict");
            }
        }
    }

    // Check for conflicts with in-memory transactions
    {
        LOCK(pool.cs); // protect pool.mapNextTx
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            COutPoint outpoint = tx.vin[i].prevout;
            if (pool.mapNextTx.count(outpoint)) {
                // Disable replacement feature for now
                return false;
            }
        }
    }


    {
        CCoinsView dummy;
        CCoinsViewCache view(&dummy);

        CAmount nValueIn = 0;
        {
            LOCK(pool.cs);
            CCoinsViewMemPool viewMemPool(pcoinsTip, pool);
            view.SetBackend(viewMemPool);

            // do we already have it?
            if (view.HaveCoins(hash))
                return false;

            // do all inputs exist?
            // Note that this does not check for the presence of actual outputs (see the next check for that),
            // only helps filling in pfMissingInputs (to determine missing vs spent).
            BOOST_FOREACH (const CTxIn txin, tx.vin) {
                if (!view.HaveCoins(txin.prevout.hash)) {
                    if (pfMissingInputs)
                        *pfMissingInputs = true;
                    return false;
                }
            }

            // are the actual inputs available?
            if (!view.HaveInputs(tx))
                return state.Invalid(error("AcceptToMemoryPool : inputs already spent"),
                    REJECT_DUPLICATE, "bad-txns-inputs-spent");

            // Bring the best block into scope
            view.GetBestBlock();

            nValueIn = view.GetValueIn(tx);

            // we have all inputs cached now, so switch back to dummy, so we don't need to keep lock on mempool
            view.SetBackend(dummy);
        }

        // Check for non-standard pay-to-script-hash in inputs
        if (Params().RequireStandard() && !AreInputsStandard(tx, view))
            return error("AcceptToMemoryPool: : nonstandard transaction input");

        // Check that the transaction doesn't have an excessive number of
        // sigops, making it impossible to mine. Since the coinbase transaction
        // itself can contain sigops MAX_TX_SIGOPS is less than
        // MAX_BLOCK_SIGOPS; we still consider this an invalid rather than
        // merely non-standard transaction.
        unsigned int nSigOps = GetLegacySigOpCount(tx);
        nSigOps += GetP2SHSigOpCount(tx, view);
        if (nSigOps > MAX_TX_SIGOPS)
            return state.DoS(0,
                error("AcceptToMemoryPool : too many sigops %s, %d > %d",
                    hash.ToString(), nSigOps, MAX_TX_SIGOPS),
                REJECT_NONSTANDARD, "bad-txns-too-many-sigops");

        CAmount nValueOut = tx.GetValueOut();
        CAmount nFees = nValueIn - nValueOut;
        double dPriority = view.GetPriority(tx, chainActive.Height());

        CTxMemPoolEntry entry(tx, nFees, GetTime(), dPriority, chainActive.Height());
        unsigned int nSize = entry.GetTxSize();

        // Don't accept it if it can't get into a block
        // but prioritise dstx and don't check fees for it
        if (mapObfuscationBroadcastTxes.count(hash)) {
            mempool.PrioritiseTransaction(hash, hash.ToString(), 1000, 0.1 * COIN);
        } else if (!ignoreFees) {
            CAmount txMinFee = GetMinRelayFee(tx, nSize, true);
            if (fLimitFree && nFees < txMinFee)
                return state.DoS(0, error("AcceptToMemoryPool : not enough fees %s, %d < %d",
                                        hash.ToString(), nFees, txMinFee),
                    REJECT_INSUFFICIENTFEE, "insufficient fee");

            // Require that free transactions have sufficient priority to be mined in the next block.
            if (GetBoolArg("-relaypriority", true) && nFees < ::minRelayTxFee.GetFee(nSize) && !AllowFree(view.GetPriority(tx, chainActive.Height() + 1))) {
                return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient priority");
            }

            // Continuously rate-limit free (really, very-low-fee) transactions
            // This mitigates 'penny-flooding' -- sending thousands of free transactions just to
            // be annoying or make others' transactions take longer to confirm.
            if (fLimitFree && nFees < ::minRelayTxFee.GetFee(nSize)) {
                static CCriticalSection csFreeLimiter;
                static double dFreeCount;
                static int64_t nLastTime;
                int64_t nNow = GetTime();

                LOCK(csFreeLimiter);

                // Use an exponentially decaying ~10-minute window:
                dFreeCount *= pow(1.0 - 1.0 / 600.0, (double)(nNow - nLastTime));
                nLastTime = nNow;
                // -limitfreerelay unit is thousand-bytes-per-minute
                // At default rate it would take over a month to fill 1GB
                if (dFreeCount >= GetArg("-limitfreerelay", 15) * 10 * 1000)
                    return state.DoS(0, error("AcceptToMemoryPool : free transaction rejected by rate limiter"),
                        REJECT_INSUFFICIENTFEE, "rate limited free transaction");
                LogPrint("mempool", "Rate limit dFreeCount: %g => %g\n", dFreeCount, dFreeCount + nSize);
                dFreeCount += nSize;
            }
        }

        if (fRejectInsaneFee && nFees > ::minRelayTxFee.GetFee(nSize) * 10000)
            return error("AcceptToMemoryPool: : insane fees %s, %d > %d",
                hash.ToString(),
                nFees, ::minRelayTxFee.GetFee(nSize) * 10000);

        // Check against previous transactions
        // This is done last to help prevent CPU exhaustion denial-of-service attacks.
        if (!CheckInputs(tx, state, view, true, STANDARD_SCRIPT_VERIFY_FLAGS, true)) {
            return error("AcceptToMemoryPool: : ConnectInputs failed %s", hash.ToString());
        }

        // Check again against just the consensus-critical mandatory script
        // verification flags, in case of bugs in the standard flags that cause
        // transactions to pass as valid when they're actually invalid. For
        // instance the STRICTENC flag was incorrectly allowing certain
        // CHECKSIG NOT scripts to pass, even though they were invalid.
        //
        // There is a similar check in CreateNewBlock() to prevent creating
        // invalid blocks, however allowing such transactions into the mempool
        // can be exploited as a DoS attack.
        if (!CheckInputs(tx, state, view, true, MANDATORY_SCRIPT_VERIFY_FLAGS, true)) {
            return error("AcceptToMemoryPool: : BUG! PLEASE REPORT THIS! ConnectInputs failed against MANDATORY but not STANDARD flags %s", hash.ToString());
        }

        // Store transaction in memory
        pool.addUnchecked(hash, entry);
    }

    SyncWithWallets(tx, NULL);

    return true;
}

bool AcceptableInputs(CTxMemPool& pool, CValidationState& state, const CTransaction& tx, bool fLimitFree, bool* pfMissingInputs, bool fRejectInsaneFee, bool isDSTX)
{
    AssertLockHeld(cs_main);
    if (pfMissingInputs)
        *pfMissingInputs = false;

    if (!CheckTransaction(tx, state))
        return error("AcceptableInputs: : CheckTransaction failed");

    // Coinbase is only valid in a block, not as a loose transaction
    if (tx.IsCoinBase())
        return state.DoS(100, error("AcceptableInputs: : coinbase as individual tx"),
            REJECT_INVALID, "coinbase");

    // Rather not work on nonstandard transactions (unless -testnet/-regtest)
    string reason;
    // for any real tx this will be checked on AcceptToMemoryPool anyway
    //    if (Params().RequireStandard() && !IsStandardTx(tx, reason))
    //        return state.DoS(0,
    //                         error("AcceptableInputs : nonstandard transaction: %s", reason),
    //                         REJECT_NONSTANDARD, reason);

    // is it already in the memory pool?
    uint256 hash = tx.GetHash();
    if (pool.exists(hash))
        return false;

    // ----------- swiftTX transaction scanning -----------

    BOOST_FOREACH (const CTxIn& in, tx.vin) {
        if (mapLockedInputs.count(in.prevout)) {
            if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                return state.DoS(0,
                    error("AcceptableInputs : conflicts with existing transaction lock: %s", reason),
                    REJECT_INVALID, "tx-lock-conflict");
            }
        }
    }

    // Check for conflicts with in-memory transactions
    {
        LOCK(pool.cs); // protect pool.mapNextTx
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            COutPoint outpoint = tx.vin[i].prevout;
            if (pool.mapNextTx.count(outpoint)) {
                // Disable replacement feature for now
                return false;
            }
        }
    }


    {
        CCoinsView dummy;
        CCoinsViewCache view(&dummy);

        CAmount nValueIn = 0;
        {
            LOCK(pool.cs);
            CCoinsViewMemPool viewMemPool(pcoinsTip, pool);
            view.SetBackend(viewMemPool);

            // do we already have it?
            if (view.HaveCoins(hash))
                return false;

            // do all inputs exist?
            // Note that this does not check for the presence of actual outputs (see the next check for that),
            // only helps filling in pfMissingInputs (to determine missing vs spent).
            BOOST_FOREACH (const CTxIn txin, tx.vin) {
                if (!view.HaveCoins(txin.prevout.hash)) {
                    if (pfMissingInputs)
                        *pfMissingInputs = true;
                    return false;
                }
            }

            // are the actual inputs available?
            if (!view.HaveInputs(tx))
                return state.Invalid(error("AcceptableInputs : inputs already spent"),
                    REJECT_DUPLICATE, "bad-txns-inputs-spent");

            // Bring the best block into scope
            view.GetBestBlock();

            nValueIn = view.GetValueIn(tx);

            // we have all inputs cached now, so switch back to dummy, so we don't need to keep lock on mempool
            view.SetBackend(dummy);
        }

        // Check for non-standard pay-to-script-hash in inputs
        // for any real tx this will be checked on AcceptToMemoryPool anyway
        //        if (Params().RequireStandard() && !AreInputsStandard(tx, view))
        //            return error("AcceptableInputs: : nonstandard transaction input");

        // Check that the transaction doesn't have an excessive number of
        // sigops, making it impossible to mine. Since the coinbase transaction
        // itself can contain sigops MAX_TX_SIGOPS is less than
        // MAX_BLOCK_SIGOPS; we still consider this an invalid rather than
        // merely non-standard transaction.
        unsigned int nSigOps = GetLegacySigOpCount(tx);
        nSigOps += GetP2SHSigOpCount(tx, view);
        if (nSigOps > MAX_TX_SIGOPS)
            return state.DoS(0,
                error("AcceptableInputs : too many sigops %s, %d > %d",
                    hash.ToString(), nSigOps, MAX_TX_SIGOPS),
                REJECT_NONSTANDARD, "bad-txns-too-many-sigops");

        CAmount nValueOut = tx.GetValueOut();
        CAmount nFees = nValueIn - nValueOut;
        double dPriority = view.GetPriority(tx, chainActive.Height());

        CTxMemPoolEntry entry(tx, nFees, GetTime(), dPriority, chainActive.Height());
        unsigned int nSize = entry.GetTxSize();

        // Don't accept it if it can't get into a block
        // but prioritise dstx and don't check fees for it
        if (isDSTX) {
            mempool.PrioritiseTransaction(hash, hash.ToString(), 1000, 0.1 * COIN);
        } else { // same as !ignoreFees for AcceptToMemoryPool
            CAmount txMinFee = GetMinRelayFee(tx, nSize, true);
            if (fLimitFree && nFees < txMinFee)
                return state.DoS(0, error("AcceptableInputs : not enough fees %s, %d < %d",
                                        hash.ToString(), nFees, txMinFee),
                    REJECT_INSUFFICIENTFEE, "insufficient fee");

            // Require that free transactions have sufficient priority to be mined in the next block.
            if (GetBoolArg("-relaypriority", true) && nFees < ::minRelayTxFee.GetFee(nSize) && !AllowFree(view.GetPriority(tx, chainActive.Height() + 1))) {
                return state.DoS(0, false, REJECT_INSUFFICIENTFEE, "insufficient priority");
            }

            // Continuously rate-limit free (really, very-low-fee) transactions
            // This mitigates 'penny-flooding' -- sending thousands of free transactions just to
            // be annoying or make others' transactions take longer to confirm.
            if (fLimitFree && nFees < ::minRelayTxFee.GetFee(nSize)) {
                static CCriticalSection csFreeLimiter;
                static double dFreeCount;
                static int64_t nLastTime;
                int64_t nNow = GetTime();

                LOCK(csFreeLimiter);

                // Use an exponentially decaying ~10-minute window:
                dFreeCount *= pow(1.0 - 1.0 / 600.0, (double)(nNow - nLastTime));
                nLastTime = nNow;
                // -limitfreerelay unit is thousand-bytes-per-minute
                // At default rate it would take over a month to fill 1GB
                if (dFreeCount >= GetArg("-limitfreerelay", 15) * 10 * 1000)
                    return state.DoS(0, error("AcceptableInputs : free transaction rejected by rate limiter"),
                        REJECT_INSUFFICIENTFEE, "rate limited free transaction");
                LogPrint("mempool", "Rate limit dFreeCount: %g => %g\n", dFreeCount, dFreeCount + nSize);
                dFreeCount += nSize;
            }
        }

        if (fRejectInsaneFee && nFees > ::minRelayTxFee.GetFee(nSize) * 10000)
            return error("AcceptableInputs: : insane fees %s, %d > %d",
                hash.ToString(),
                nFees, ::minRelayTxFee.GetFee(nSize) * 10000);

        // Check against previous transactions
        // This is done last to help prevent CPU exhaustion denial-of-service attacks.
        if (!CheckInputs(tx, state, view, false, STANDARD_SCRIPT_VERIFY_FLAGS, true)) {
            return error("AcceptableInputs: : ConnectInputs failed %s", hash.ToString());
        }

        // Check again against just the consensus-critical mandatory script
        // verification flags, in case of bugs in the standard flags that cause
        // transactions to pass as valid when they're actually invalid. For
        // instance the STRICTENC flag was incorrectly allowing certain
        // CHECKSIG NOT scripts to pass, even though they were invalid.
        //
        // There is a similar check in CreateNewBlock() to prevent creating
        // invalid blocks, however allowing such transactions into the mempool
        // can be exploited as a DoS attack.
        // for any real tx this will be checked on AcceptToMemoryPool anyway
        //        if (!CheckInputs(tx, state, view, false, MANDATORY_SCRIPT_VERIFY_FLAGS, true))
        //        {
        //            return error("AcceptableInputs: : BUG! PLEASE REPORT THIS! ConnectInputs failed against MANDATORY but not STANDARD flags %s", hash.ToString());
        //        }

        // Store transaction in memory
        // pool.addUnchecked(hash, entry);
    }

    // SyncWithWallets(tx, NULL);

    return true;
}

/** Return transaction in tx, and if it was found inside a block, its hash is placed in hashBlock */
bool GetTransaction(const uint256& hash, CTransaction& txOut, uint256& hashBlock, bool fAllowSlow)
{
    CBlockIndex* pindexSlow = NULL;
    {
        LOCK(cs_main);
        {
            if (mempool.lookup(hash, txOut)) {
                return true;
            }
        }

        if (fTxIndex) {
            CDiskTxPos postx;
            if (pblocktree->ReadTxIndex(hash, postx)) {
                CAutoFile file(OpenBlockFile(postx, true), SER_DISK, CLIENT_VERSION);
                if (file.IsNull())
                    return error("%s: OpenBlockFile failed", __func__);
                CBlockHeader header;
                try {
                    file >> header;
                    fseek(file.Get(), postx.nTxOffset, SEEK_CUR);
                    file >> txOut;
                } catch (std::exception& e) {
                    return error("%s : Deserialize or I/O error - %s", __func__, e.what());
                }
                hashBlock = header.GetHash();
                if (txOut.GetHash() != hash)
                    return error("%s : txid mismatch", __func__);
                return true;
            }
        }

        if (fAllowSlow) { // use coin database to locate block that contains transaction, and scan it
            int nHeight = -1;
            {
                CCoinsViewCache& view = *pcoinsTip;
                const CCoins* coins = view.AccessCoins(hash);
                if (coins)
                    nHeight = coins->nHeight;
            }
            if (nHeight > 0)
                pindexSlow = chainActive[nHeight];
        }
    }

    if (pindexSlow) {
        CBlock block;
        if (ReadBlockFromDisk(block, pindexSlow)) {
            BOOST_FOREACH (const CTransaction& tx, block.vtx) {
                if (tx.GetHash() == hash) {
                    txOut = tx;
                    hashBlock = pindexSlow->GetBlockHash();
                    return true;
                }
            }
        }
    }

    return false;
}


//////////////////////////////////////////////////////////////////////////////
//
// CBlock and CBlockIndex
//

bool WriteBlockToDisk(CBlock& block, CDiskBlockPos& pos)
{
    // Open history file to append
    CAutoFile fileout(OpenBlockFile(pos), SER_DISK, CLIENT_VERSION);
    if (fileout.IsNull())
        return error("WriteBlockToDisk : OpenBlockFile failed");

    // Write index header
    unsigned int nSize = fileout.GetSerializeSize(block);
    fileout << FLATDATA(Params().MessageStart()) << nSize;

    // Write block
    long fileOutPos = ftell(fileout.Get());
    if (fileOutPos < 0)
        return error("WriteBlockToDisk : ftell failed");
    pos.nPos = (unsigned int)fileOutPos;
    fileout << block;

    return true;
}

bool ReadBlockFromDisk(CBlock& block, const CDiskBlockPos& pos)
{
    block.SetNull();

    // Open history file to read
    CAutoFile filein(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION);
    if (filein.IsNull())
        return error("ReadBlockFromDisk : OpenBlockFile failed");

    // Read block
    try {
        filein >> block;
    } catch (std::exception& e) {
        return error("%s : Deserialize or I/O error - %s", __func__, e.what());
    }

    // Check the header
    if (block.IsProofOfWork()) {
        if (!CheckProofOfWork(block.GetHash(), block.nBits))
            return error("ReadBlockFromDisk : Errors in block header");
    }

    return true;
}

bool ReadBlockFromDisk(CBlock& block, const CBlockIndex* pindex)
{
    if (!ReadBlockFromDisk(block, pindex->GetBlockPos()))
        return false;
    if (block.GetHash() != pindex->GetBlockHash()) {
        LogPrintf("%s : block=%s index=%s\n", __func__, block.GetHash().ToString().c_str(), pindex->GetBlockHash().ToString().c_str());
        return error("ReadBlockFromDisk(CBlock&, CBlockIndex*) : GetHash() doesn't match index");
    }
    return true;
}


double ConvertBitsToDouble(unsigned int nBits)
{
    int nShift = (nBits >> 24) & 0xff;

    double dDiff =
        (double)0x0000ffff / (double)(nBits & 0x00ffffff);

    while (nShift < 29) {
        dDiff *= 256.0;
        nShift++;
    }
    while (nShift > 29) {
        dDiff /= 256.0;
        nShift--;
    }

    return dDiff;
}

int64_t GetBlockValue(int nHeight)
{
    int64_t nSubsidy = 0;


	if (nHeight == 0) {
		nSubsidy = 210000 * COIN;
	}else if (nHeight <= 1000) { //Before v1.1.0.0
		nSubsidy = 0.1 * COIN;
	}else if (nHeight <= 21160) { //Before v1.1.0.0
		nSubsidy = 0.7 * COIN;
	}else if (nHeight <= 31240) { //Before v1.1.0.0
		nSubsidy = 2 * COIN;
	}else if (nHeight <= 41320) { //Before v1.1.0.0
		nSubsidy = 2.5 * COIN;
	}else if (nHeight <= 51400 && nHeight > 41320) { // 7 days
		nSubsidy = 3 * COIN;
	}else if (nHeight <= 61480 && nHeight > 51400) { // 7 days
		nSubsidy = 3.5 * COIN;
	}else if (nHeight <= 71560 && nHeight > 61480) { // 7 days
		nSubsidy = 4 * COIN;
	}else if (nHeight <= 81640 && nHeight > 71560) { // 7 days
		nSubsidy = 4.5 * COIN;
	}else if (nHeight <= 91720 && nHeight > 81640) { // 7 days
		nSubsidy = 5 * COIN;
	}else if (nHeight <= 101800 && nHeight > 91720) { // 7 days
		nSubsidy = 5.5 * COIN;
	}else if (nHeight <= 111880 && nHeight > 101800) { // 7 days
		nSubsidy = 6 * COIN;
	}else if (nHeight <= 121960 && nHeight > 111880) { // 7 days
		nSubsidy = 6.5 * COIN;
	}else if (nHeight <= 132040 && nHeight > 121960) { // 7 days
		nSubsidy = 7 * COIN;
	}else if (nHeight <= 142120 && nHeight > 132040) { // 7 days
		nSubsidy = 7.5 * COIN;
	}else if (nHeight <= 146440 && nHeight > 142120) { // 3 days 142120 - 146440
		nSubsidy = 0.1 * COIN;
	}else if (nHeight <= 156520 && nHeight > 146440) { // 7 days 146440 - 156520
		nSubsidy = 8 * COIN;
	}else if (nHeight <= 166600 && nHeight > 156520) { // 7 days 156520 - 166600
		nSubsidy = 8.5 * COIN;
	}else if (nHeight <= 176680 && nHeight > 166600) { // 7 days 166600 - 176680
		nSubsidy = 9 * COIN;
	}else if (nHeight <= 186760 && nHeight > 176680) { // 4 years 176680 - 186760
		nSubsidy = 9.5 * COIN;
	}else if (nHeight > 186760) { // Till Max Supply 186760 - oo
		nSubsidy = 10 * COIN;
	}
    
    // Check if we reached the coin max supply.
    int64_t nMoneySupply = chainActive.Tip()->nMoneySupply;
	if (nMoneySupply + nSubsidy >= Params().MaxMoneyOut())
        nSubsidy = Params().MaxMoneyOut() - nMoneySupply;
    if (nMoneySupply >= Params().MaxMoneyOut())
        nSubsidy = 0;
	return nSubsidy;
}

int64_t GetMasternodePayment(int nHeight, int64_t blockValue, int nMasternodeCount)
{
    int64_t ret = 0;

    if (nHeight < 101) {
        ret = blockValue * 0;
    }   else {
        ret = blockValue * 0.8; //80% for nodes
    }

	return ret;

}

bool IsInitialBlockDownload()
{
    LOCK(cs_main);
    if (fImporting || fReindex || chainActive.Height() < Checkpoints::GetTotalBlocksEstimate())
        return true;
    static bool lockIBDState = false;
    if (lockIBDState)
        return false;
    bool state = (chainActive.Height() < pindexBestHeader->nHeight - 24 * 6 ||
                  pindexBestHeader->GetBlockTime() < GetTime() - 6 * 60 * 60); // ~144 blocks behind -> 2 x fork detection time
    if (!state)
        lockIBDState = true;
    return state;
}

bool fLargeWorkForkFound = false;
bool fLargeWorkInvalidChainFound = false;
CBlockIndex *pindexBestForkTip = NULL, *pindexBestForkBase = NULL;

void CheckForkWarningConditions()
{
    AssertLockHeld(cs_main);
    // Before we get past initial download, we cannot reliably alert about forks
    // (we assume we don't get stuck on a fork before the last checkpoint)
    if (IsInitialBlockDownload())
        return;

    // If our best fork is no longer within 72 blocks (+/- 3 hours if no one mines it)
    // of our head, drop it
    if (pindexBestForkTip && chainActive.Height() - pindexBestForkTip->nHeight >= 72)
        pindexBestForkTip = NULL;

    if (pindexBestForkTip || (pindexBestInvalid && pindexBestInvalid->nChainWork > chainActive.Tip()->nChainWork + (GetBlockProof(*chainActive.Tip()) * 6))) {
        if (!fLargeWorkForkFound && pindexBestForkBase) {
            if (pindexBestForkBase->phashBlock) {
                std::string warning = std::string("'Warning: Large-work fork detected, forking after block ") +
                                      pindexBestForkBase->phashBlock->ToString() + std::string("'");
                CAlert::Notify(warning, true);
            }
        }
        if (pindexBestForkTip && pindexBestForkBase) {
            if (pindexBestForkBase->phashBlock) {
                LogPrintf("CheckForkWarningConditions: Warning: Large valid fork found\n  forking the chain at height %d (%s)\n  lasting to height %d (%s).\nChain state database corruption likely.\n",
                    pindexBestForkBase->nHeight, pindexBestForkBase->phashBlock->ToString(),
                    pindexBestForkTip->nHeight, pindexBestForkTip->phashBlock->ToString());
                fLargeWorkForkFound = true;
            }
        } else {
            LogPrintf("CheckForkWarningConditions: Warning: Found invalid chain at least ~6 blocks longer than our best chain.\nChain state database corruption likely.\n");
            fLargeWorkInvalidChainFound = true;
        }
    } else {
        fLargeWorkForkFound = false;
        fLargeWorkInvalidChainFound = false;
    }
}

void CheckForkWarningConditionsOnNewFork(CBlockIndex* pindexNewForkTip)
{
    AssertLockHeld(cs_main);
    // If we are on a fork that is sufficiently large, set a warning flag
    CBlockIndex* pfork = pindexNewForkTip;
    CBlockIndex* plonger = chainActive.Tip();
    while (pfork && pfork != plonger) {
        while (plonger && plonger->nHeight > pfork->nHeight)
            plonger = plonger->pprev;
        if (pfork == plonger)
            break;
        pfork = pfork->pprev;
    }

    // We define a condition which we should warn the user about as a fork of at least 7 blocks
    // who's tip is within 72 blocks (+/- 3 hours if no one mines it) of ours
    // or a chain that is entirely longer than ours and invalid (note that this should be detected by both)
    // We use 7 blocks rather arbitrarily as it represents just under 10% of sustained network
    // hash rate operating on the fork.
    // We define it this way because it allows us to only store the highest fork tip (+ base) which meets
    // the 7-block condition and from this always have the most-likely-to-cause-warning fork
    if (pfork && (!pindexBestForkTip || (pindexBestForkTip && pindexNewForkTip->nHeight > pindexBestForkTip->nHeight)) &&
        pindexNewForkTip->nChainWork - pfork->nChainWork > (GetBlockProof(*pfork) * 7) &&
        chainActive.Height() - pindexNewForkTip->nHeight < 72) {
        pindexBestForkTip = pindexNewForkTip;
        pindexBestForkBase = pfork;
    }

    CheckForkWarningConditions();
}

// Requires cs_main.
void Misbehaving(NodeId pnode, int howmuch)
{
    if (howmuch == 0)
        return;

    CNodeState* state = State(pnode);
    if (state == NULL)
        return;

    state->nMisbehavior += howmuch;
    int banscore = GetArg("-banscore", 100);
    if (state->nMisbehavior >= banscore && state->nMisbehavior - howmuch < banscore) {
        LogPrintf("Misbehaving: %s (%d -> %d) BAN THRESHOLD EXCEEDED\n", state->name, state->nMisbehavior - howmuch, state->nMisbehavior);
        state->fShouldBan = false;
    } else
        LogPrintf("Misbehaving: %s (%d -> %d)\n", state->name, state->nMisbehavior - howmuch, state->nMisbehavior);
}

void static InvalidChainFound(CBlockIndex* pindexNew)
{
    if (!pindexBestInvalid || pindexNew->nChainWork > pindexBestInvalid->nChainWork)
        pindexBestInvalid = pindexNew;

    LogPrintf("InvalidChainFound: invalid block=%s  height=%d  log2_work=%.8g  date=%s\n",
        pindexNew->GetBlockHash().ToString(), pindexNew->nHeight,
        log(pindexNew->nChainWork.getdouble()) / log(2.0), DateTimeStrFormat("%Y-%m-%d %H:%M:%S",
                                                               pindexNew->GetBlockTime()));
    LogPrintf("InvalidChainFound:  current best=%s  height=%d  log2_work=%.8g  date=%s\n",
        chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(), log(chainActive.Tip()->nChainWork.getdouble()) / log(2.0),
        DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()));
    CheckForkWarningConditions();
}

void static InvalidBlockFound(CBlockIndex* pindex, const CValidationState& state)
{
    int nDoS = 0;
    if (state.IsInvalid(nDoS)) {
        std::map<uint256, NodeId>::iterator it = mapBlockSource.find(pindex->GetBlockHash());
        if (it != mapBlockSource.end() && State(it->second)) {
            CBlockReject reject = {state.GetRejectCode(), state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), pindex->GetBlockHash()};
            State(it->second)->rejects.push_back(reject);
            if (nDoS > 0)
                Misbehaving(it->second, nDoS);
        }
    }
    if (!state.CorruptionPossible()) {
        pindex->nStatus |= BLOCK_FAILED_VALID;
        setDirtyBlockIndex.insert(pindex);
        setBlockIndexCandidates.erase(pindex);
        InvalidChainFound(pindex);
    }
}

void UpdateCoins(const CTransaction& tx, CValidationState& state, CCoinsViewCache& inputs, CTxUndo& txundo, int nHeight)
{
    // mark inputs spent
    if (!tx.IsCoinBase()) {
        txundo.vprevout.reserve(tx.vin.size());
        BOOST_FOREACH (const CTxIn& txin, tx.vin) {
            txundo.vprevout.push_back(CTxInUndo());
            bool ret = inputs.ModifyCoins(txin.prevout.hash)->Spend(txin.prevout, txundo.vprevout.back());
            assert(ret);
        }
    }

    // add outputs
    inputs.ModifyCoins(tx.GetHash())->FromTx(tx, nHeight);
}

bool CScriptCheck::operator()()
{
    const CScript& scriptSig = ptxTo->vin[nIn].scriptSig;
    if (!VerifyScript(scriptSig, scriptPubKey, nFlags, CachingTransactionSignatureChecker(ptxTo, nIn, cacheStore), &error)) {
        return ::error("CScriptCheck(): %s:%d VerifySignature failed: %s", ptxTo->GetHash().ToString(), nIn, ScriptErrorString(error));
    }
    return true;
}

bool CheckInputs(const CTransaction& tx, CValidationState& state, const CCoinsViewCache& inputs, bool fScriptChecks, unsigned int flags, bool cacheStore, std::vector<CScriptCheck>* pvChecks)
{
    if (!tx.IsCoinBase()) {
        if (pvChecks)
            pvChecks->reserve(tx.vin.size());

        // This doesn't trigger the DoS code on purpose; if it did, it would make it easier
        // for an attacker to attempt to split the network.
        if (!inputs.HaveInputs(tx))
            return state.Invalid(error("CheckInputs() : %s inputs unavailable", tx.GetHash().ToString()));

        // While checking, GetBestBlock() refers to the parent block.
        // This is also true for mempool checks.
        CBlockIndex* pindexPrev = mapBlockIndex.find(inputs.GetBestBlock())->second;
        int nSpendHeight = pindexPrev->nHeight + 1;
        CAmount nValueIn = 0;
        CAmount nFees = 0;
        for (unsigned int i = 0; i < tx.vin.size(); i++) {
            const COutPoint& prevout = tx.vin[i].prevout;
            const CCoins* coins = inputs.AccessCoins(prevout.hash);
            assert(coins);

            // If prev is coinbase, check that it's matured
            if (coins->IsCoinBase() || coins->IsCoinStake()) {
                if (nSpendHeight - coins->nHeight < Params().COINBASE_MATURITY())
                    return state.Invalid(
                        error("CheckInputs() : tried to spend coinbase at depth %d, coinstake=%d", nSpendHeight - coins->nHeight, coins->IsCoinStake()),
                        REJECT_INVALID, "bad-txns-premature-spend-of-coinbase");
            }

            // Check for negative or overflow input values
            nValueIn += coins->vout[prevout.n].nValue;
            if (!MoneyRange(coins->vout[prevout.n].nValue) || !MoneyRange(nValueIn))
                return state.DoS(100, error("CheckInputs() : txin values out of range"),
                    REJECT_INVALID, "bad-txns-inputvalues-outofrange");
        }

        if (!tx.IsCoinStake()) {
            if (nValueIn < tx.GetValueOut())
                return state.DoS(100, error("CheckInputs() : %s value in (%s) < value out (%s)",
                                          tx.GetHash().ToString(), FormatMoney(nValueIn), FormatMoney(tx.GetValueOut())),
                    REJECT_INVALID, "bad-txns-in-belowout");

            // Tally transaction fees
            CAmount nTxFee = nValueIn - tx.GetValueOut();
            if (nTxFee < 0)
                return state.DoS(100, error("CheckInputs() : %s nTxFee < 0", tx.GetHash().ToString()),
                    REJECT_INVALID, "bad-txns-fee-negative");
            nFees += nTxFee;
            if (!MoneyRange(nFees))
                return state.DoS(100, error("CheckInputs() : nFees out of range"),
                    REJECT_INVALID, "bad-txns-fee-outofrange");
        }
        // The first loop above does all the inexpensive checks.
        // Only if ALL inputs pass do we perform expensive ECDSA signature checks.
        // Helps prevent CPU exhaustion attacks.

        // Skip ECDSA signature verification when connecting blocks
        // before the last block chain checkpoint. This is safe because block merkle hashes are
        // still computed and checked, and any change will be caught at the next checkpoint.
        if (fScriptChecks) {
            for (unsigned int i = 0; i < tx.vin.size(); i++) {
                const COutPoint& prevout = tx.vin[i].prevout;
                const CCoins* coins = inputs.AccessCoins(prevout.hash);
                assert(coins);

                // Verify signature
                CScriptCheck check(*coins, tx, i, flags, cacheStore);
                if (pvChecks) {
                    pvChecks->push_back(CScriptCheck());
                    check.swap(pvChecks->back());
                } else if (!check()) {
                    if (flags & STANDARD_NOT_MANDATORY_VERIFY_FLAGS) {
                        // Check whether the failure was caused by a
                        // non-mandatory script verification check, such as
                        // non-standard DER encodings or non-null dummy
                        // arguments; if so, don't trigger DoS protection to
                        // avoid splitting the network between upgraded and
                        // non-upgraded nodes.
                        CScriptCheck check(*coins, tx, i,
                            flags & ~STANDARD_NOT_MANDATORY_VERIFY_FLAGS, cacheStore);
                        if (check())
                            return state.Invalid(false, REJECT_NONSTANDARD, strprintf("non-mandatory-script-verify-flag (%s)", ScriptErrorString(check.GetScriptError())));
                    }
                    // Failures of other flags indicate a transaction that is
                    // invalid in new blocks, e.g. a invalid P2SH. We DoS ban
                    // such nodes as they are not following the protocol. That
                    // said during an upgrade careful thought should be taken
                    // as to the correct behavior - we may want to continue
                    // peering with non-upgraded nodes even after a soft-fork
                    // super-majority vote has passed.
                    return state.DoS(100, false, REJECT_INVALID, strprintf("mandatory-script-verify-flag-failed (%s)", ScriptErrorString(check.GetScriptError())));
                }
            }
        }
    }

    return true;
}

bool DisconnectBlock(CBlock& block, CValidationState& state, CBlockIndex* pindex, CCoinsViewCache& view, bool* pfClean)
{
    assert(pindex->GetBlockHash() == view.GetBestBlock());

    if (pfClean)
        *pfClean = false;

    bool fClean = true;

    CBlockUndo blockUndo;
    CDiskBlockPos pos = pindex->GetUndoPos();
    if (pos.IsNull())
        return error("DisconnectBlock() : no undo data available");
    if (!blockUndo.ReadFromDisk(pos, pindex->pprev->GetBlockHash()))
        return error("DisconnectBlock() : failure reading undo data");

    if (blockUndo.vtxundo.size() + 1 != block.vtx.size())
        return error("DisconnectBlock() : block and undo data inconsistent");

    // undo transactions in reverse order
    for (int i = block.vtx.size() - 1; i >= 0; i--) {
        const CTransaction& tx = block.vtx[i];
        uint256 hash = tx.GetHash();

        // Check that all outputs are available and match the outputs in the block itself
        // exactly. Note that transactions with only provably unspendable outputs won't
        // have outputs available even in the block itself, so we handle that case
        // specially with outsEmpty.
        {
            CCoins outsEmpty;
            CCoinsModifier outs = view.ModifyCoins(hash);
            outs->ClearUnspendable();

            CCoins outsBlock(tx, pindex->nHeight);
            // The CCoins serialization does not serialize negative numbers.
            // No network rules currently depend on the version here, so an inconsistency is harmless
            // but it must be corrected before txout nversion ever influences a network rule.
            if (outsBlock.nVersion < 0)
                outs->nVersion = outsBlock.nVersion;
            if (*outs != outsBlock)
                fClean = fClean && error("DisconnectBlock() : added transaction mismatch? database corrupted");

            // remove outputs
            outs->Clear();
        }

        // restore inputs
        if (i > 0) { // not coinbases
            const CTxUndo& txundo = blockUndo.vtxundo[i - 1];
            if (txundo.vprevout.size() != tx.vin.size())
                return error("DisconnectBlock() : transaction and undo data inconsistent - txundo.vprevout.siz=%d tx.vin.siz=%d", txundo.vprevout.size(), tx.vin.size());
            for (unsigned int j = tx.vin.size(); j-- > 0;) {
                const COutPoint& out = tx.vin[j].prevout;
                const CTxInUndo& undo = txundo.vprevout[j];
                CCoinsModifier coins = view.ModifyCoins(out.hash);
                if (undo.nHeight != 0) {
                    // undo data contains height: this is the last output of the prevout tx being spent
                    if (!coins->IsPruned())
                        fClean = fClean && error("DisconnectBlock() : undo data overwriting existing transaction");
                    coins->Clear();
                    coins->fCoinBase = undo.fCoinBase;
                    coins->nHeight = undo.nHeight;
                    coins->nVersion = undo.nVersion;
                } else {
                    if (coins->IsPruned())
                        fClean = fClean && error("DisconnectBlock() : undo data adding output to missing transaction");
                }
                if (coins->IsAvailable(out.n))
                    fClean = fClean && error("DisconnectBlock() : undo data overwriting existing output");
                if (coins->vout.size() < out.n + 1)
                    coins->vout.resize(out.n + 1);
                coins->vout[out.n] = undo.txout;

				// erase the spent input
				mapStakeSpent.erase(out);
            }
        }
    }

    // move best block pointer to prevout block
    view.SetBestBlock(pindex->pprev->GetBlockHash());

    if (pfClean) {
        *pfClean = fClean;
        return true;
    } else {
        return fClean;
    }
}

void static FlushBlockFile(bool fFinalize = false)
{
    LOCK(cs_LastBlockFile);

    CDiskBlockPos posOld(nLastBlockFile, 0);

    FILE* fileOld = OpenBlockFile(posOld);
    if (fileOld) {
        if (fFinalize)
            TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nSize);
        FileCommit(fileOld);
        fclose(fileOld);
    }

    fileOld = OpenUndoFile(posOld);
    if (fileOld) {
        if (fFinalize)
            TruncateFile(fileOld, vinfoBlockFile[nLastBlockFile].nUndoSize);
        FileCommit(fileOld);
        fclose(fileOld);
    }
}

bool FindUndoPos(CValidationState& state, int nFile, CDiskBlockPos& pos, unsigned int nAddSize);

static CCheckQueue<CScriptCheck> scriptcheckqueue(128);

void ThreadScriptCheck()
{
    RenameThread("altbet-scriptch");
    scriptcheckqueue.Thread();
}

static int64_t nTimeVerify = 0;
static int64_t nTimeConnect = 0;
static int64_t nTimeIndex = 0;
static int64_t nTimeCallbacks = 0;
static int64_t nTimeTotal = 0;

bool ConnectBlock(const CBlock& block, CValidationState& state, CBlockIndex* pindex, CCoinsViewCache& view, bool fJustCheck)
{
    AssertLockHeld(cs_main);
    // Check it again in case a previous version let a bad block in
    if (!CheckBlock(block, state, !fJustCheck, !fJustCheck))
        return false;

    // verify that the view's current state corresponds to the previous block
    uint256 hashPrevBlock = pindex->pprev == NULL ? uint256(0) : pindex->pprev->GetBlockHash();
    if (hashPrevBlock != view.GetBestBlock())
        LogPrintf("%s: hashPrev=%s view=%s\n", __func__, hashPrevBlock.ToString().c_str(), view.GetBestBlock().ToString().c_str());
    assert(hashPrevBlock == view.GetBestBlock());

    // Special case for the genesis block, skipping connection of its transactions
    // (its coinbase is unspendable)
    if (block.GetHash() == Params().HashGenesisBlock()) {
        view.SetBestBlock(pindex->GetBlockHash());
        return true;
    }

    if (pindex->nHeight <= Params().LAST_POW_BLOCK() && block.IsProofOfStake())
        return state.DoS(100, error("ConnectBlock() : PoS period not active"),
            REJECT_INVALID, "PoS-early");

    if (pindex->nHeight > Params().LAST_POW_BLOCK() && block.IsProofOfWork())
        return state.DoS(100, error("ConnectBlock() : PoW period ended"),
            REJECT_INVALID, "PoW-ended");

    bool fScriptChecks = pindex->nHeight >= Checkpoints::GetTotalBlocksEstimate();

    // Do not allow blocks that contain transactions which 'overwrite' older transactions,
    // unless those are already completely spent.
    // If such overwrites are allowed, coinbases and transactions depending upon those
    // can be duplicated to remove the ability to spend the first instance -- even after
    // being sent to another address.
    // See BIP30 and http://r6.ca/blog/20120206T005236Z.html for more information.
    // This logic is not necessary for memory pool transactions, as AcceptToMemoryPool
    // already refuses previously-known transaction ids entirely.
    // This rule was originally applied all blocks whose timestamp was after March 15, 2012, 0:00 UTC.
    // Now that the whole chain is irreversibly beyond that time it is applied to all blocks except the
    // two in the chain that violate it. This prevents exploiting the issue against nodes in their
    // initial block download.
    bool fEnforceBIP30 = (!pindex->phashBlock) || // Enforce on CreateNewBlock invocations which don't have a hash.
                         !((pindex->nHeight == 91842 && pindex->GetBlockHash() == uint256("0x00000000000a4d0a398161ffc163c503763b1f4360639393e0e4c8e300e0caec")) ||
                             (pindex->nHeight == 91880 && pindex->GetBlockHash() == uint256("0x00000000000743f190a18c5577a3c2d2a1f610ae9601ac046a38084ccb7cd721")));
    if (fEnforceBIP30) {
        BOOST_FOREACH (const CTransaction& tx, block.vtx) {
            const CCoins* coins = view.AccessCoins(tx.GetHash());
            if (coins && !coins->IsPruned())
                return state.DoS(100, error("ConnectBlock() : tried to overwrite transaction"),
                    REJECT_INVALID, "bad-txns-BIP30");
        }
    }

    // BIP16 didn't become active until Apr 1 2012
    int64_t nBIP16SwitchTime = 1333238400;
    bool fStrictPayToScriptHash = (pindex->GetBlockTime() >= nBIP16SwitchTime);

    unsigned int flags = fStrictPayToScriptHash ? SCRIPT_VERIFY_P2SH : SCRIPT_VERIFY_NONE;

    // Start enforcing the DERSIG (BIP66) rules, for block.nVersion=3 blocks, when 75% of the network has upgraded:
    if (block.nVersion >= 3 && CBlockIndex::IsSuperMajority(3, pindex->pprev, Params().EnforceBlockUpgradeMajority())) {
        flags |= SCRIPT_VERIFY_DERSIG;
    }

    CBlockUndo blockundo;

    CCheckQueueControl<CScriptCheck> control(fScriptChecks && nScriptCheckThreads ? &scriptcheckqueue : NULL);

    int64_t nTimeStart = GetTimeMicros();
    CAmount nFees = 0;
    int nInputs = 0;
    unsigned int nSigOps = 0;
    CDiskTxPos pos(pindex->GetBlockPos(), GetSizeOfCompactSize(block.vtx.size()));
    std::vector<std::pair<uint256, CDiskTxPos> > vPos;
    vPos.reserve(block.vtx.size());
    blockundo.vtxundo.reserve(block.vtx.size() - 1);
    CAmount nValueOut = 0;
    CAmount nValueIn = 0;
    for (unsigned int i = 0; i < block.vtx.size(); i++) {
        const CTransaction& tx = block.vtx[i];

        nInputs += tx.vin.size();
        nSigOps += GetLegacySigOpCount(tx);
        if (nSigOps > MAX_BLOCK_SIGOPS)
            return state.DoS(100, error("ConnectBlock() : too many sigops"),
                REJECT_INVALID, "bad-blk-sigops");

        if (!tx.IsCoinBase()) {
            if (!view.HaveInputs(tx))
                return state.DoS(100, error("ConnectBlock() : inputs missing/spent"),
                    REJECT_INVALID, "bad-txns-inputs-missingorspent");

            if (fStrictPayToScriptHash) {
                // Add in sigops done by pay-to-script-hash inputs;
                // this is to prevent a "rogue miner" from creating
                // an incredibly-expensive-to-validate block.
                nSigOps += GetP2SHSigOpCount(tx, view);
                if (nSigOps > MAX_BLOCK_SIGOPS)
                    return state.DoS(100, error("ConnectBlock() : too many sigops"),
                        REJECT_INVALID, "bad-blk-sigops");
            }

            if (!tx.IsCoinStake())
                nFees += view.GetValueIn(tx) - tx.GetValueOut();
            nValueIn += view.GetValueIn(tx);

            std::vector<CScriptCheck> vChecks;
            if (!CheckInputs(tx, state, view, fScriptChecks, flags, false, nScriptCheckThreads ? &vChecks : NULL))
                return false;
            control.Add(vChecks);
        }
        nValueOut += tx.GetValueOut();

        CTxUndo undoDummy;
        if (i > 0) {
            blockundo.vtxundo.push_back(CTxUndo());
        }
        UpdateCoins(tx, state, view, i == 0 ? undoDummy : blockundo.vtxundo.back(), pindex->nHeight);

        vPos.push_back(std::make_pair(tx.GetHash(), pos));
        pos.nTxOffset += ::GetSerializeSize(tx, SER_DISK, CLIENT_VERSION);
    }

    // ppcoin: track money supply and mint amount info
    CAmount nMoneySupplyPrev = pindex->pprev ? pindex->pprev->nMoneySupply : 0;
    pindex->nMoneySupply = nMoneySupplyPrev + nValueOut - nValueIn;
    pindex->nMint = pindex->nMoneySupply - nMoneySupplyPrev;

    if (!pblocktree->WriteBlockIndex(CDiskBlockIndex(pindex)))
        return error("Connect() : WriteBlockIndex for pindex failed");

    int64_t nTime1 = GetTimeMicros();
    nTimeConnect += nTime1 - nTimeStart;
    LogPrint("bench", "      - Connect %u transactions: %.2fms (%.3fms/tx, %.3fms/txin) [%.2fs]\n", (unsigned)block.vtx.size(), 0.001 * (nTime1 - nTimeStart), 0.001 * (nTime1 - nTimeStart) / block.vtx.size(), nInputs <= 1 ? 0 : 0.001 * (nTime1 - nTimeStart) / (nInputs - 1), nTimeConnect * 0.000001);

    //PoW phase redistributed fees to miner. PoS stage destroys fees.
    CAmount nExpectedMint = GetBlockValue(pindex->pprev->nHeight);
    if (block.IsProofOfWork())
        nExpectedMint += nFees;

    if (!IsBlockValueValid(block, nExpectedMint, pindex->nMint)) {
        return state.DoS(100,
            error("ConnectBlock() : reward pays too much (actual=%s vs limit=%s)",
                FormatMoney(pindex->nMint), FormatMoney(nExpectedMint)),
            REJECT_INVALID, "bad-cb-amount");
    }

    if (!control.Wait())
        return state.DoS(100, false);
    int64_t nTime2 = GetTimeMicros();
    nTimeVerify += nTime2 - nTimeStart;
    LogPrint("bench", "    - Verify %u txins: %.2fms (%.3fms/txin) [%.2fs]\n", nInputs - 1, 0.001 * (nTime2 - nTimeStart), nInputs <= 1 ? 0 : 0.001 * (nTime2 - nTimeStart) / (nInputs - 1), nTimeVerify * 0.000001);

    if (fJustCheck)
        return true;

    // Write undo information to disk
    if (pindex->GetUndoPos().IsNull() || !pindex->IsValid(BLOCK_VALID_SCRIPTS)) {
        if (pindex->GetUndoPos().IsNull()) {
            CDiskBlockPos pos;
            if (!FindUndoPos(state, pindex->nFile, pos, ::GetSerializeSize(blockundo, SER_DISK, CLIENT_VERSION) + 40))
                return error("ConnectBlock() : FindUndoPos failed");
            if (!blockundo.WriteToDisk(pos, pindex->pprev->GetBlockHash()))
                return state.Abort("Failed to write undo data");

            // update nUndoPos in block index
            pindex->nUndoPos = pos.nPos;
            pindex->nStatus |= BLOCK_HAVE_UNDO;
        }

        pindex->RaiseValidity(BLOCK_VALID_SCRIPTS);
        setDirtyBlockIndex.insert(pindex);
    }

    if (fTxIndex)
        if (!pblocktree->WriteTxIndex(vPos))
            return state.Abort("Failed to write transaction index");

	// add new entries
	for (const CTransaction tx : block.vtx) {
		//if (tx.IsCoinBase() || tx.IsZerocoinSpend())
		if (tx.IsCoinBase())
			continue;
		for (const CTxIn in : tx.vin) {
			mapStakeSpent.insert(std::make_pair(in.prevout, pindex->nHeight));
		}
	}

	// delete old entries
	for (auto it = mapStakeSpent.begin(); it != mapStakeSpent.end(); ++it) {
		if (it->second < pindex->nHeight - Params().MaxReorganizationDepth()) {
			mapStakeSpent.erase(it->first);
		}
	}

    // add this block to the view's block chain
    view.SetBestBlock(pindex->GetBlockHash());

    int64_t nTime3 = GetTimeMicros();
    nTimeIndex += nTime3 - nTime2;
    LogPrint("bench", "    - Index writing: %.2fms [%.2fs]\n", 0.001 * (nTime3 - nTime2), nTimeIndex * 0.000001);

    // Watch for changes to the previous coinbase transaction.
    static uint256 hashPrevBestCoinBase;
    g_signals.UpdatedTransaction(hashPrevBestCoinBase);
    hashPrevBestCoinBase = block.vtx[0].GetHash();

    int64_t nTime4 = GetTimeMicros();
    nTimeCallbacks += nTime4 - nTime3;
    LogPrint("bench", "    - Callbacks: %.2fms [%.2fs]\n", 0.001 * (nTime4 - nTime3), nTimeCallbacks * 0.000001);

    return true;
}

enum FlushStateMode {
    FLUSH_STATE_IF_NEEDED,
    FLUSH_STATE_PERIODIC,
    FLUSH_STATE_ALWAYS
};

/**
 * Update the on-disk chain state.
 * The caches and indexes are flushed if either they're too large, forceWrite is set, or
 * fast is not set and it's been a while since the last write.
 */
bool static FlushStateToDisk(CValidationState& state, FlushStateMode mode)
{
    LOCK(cs_main);
    static int64_t nLastWrite = 0;
    try {
        if ((mode == FLUSH_STATE_ALWAYS) ||
            ((mode == FLUSH_STATE_PERIODIC || mode == FLUSH_STATE_IF_NEEDED) && pcoinsTip->GetCacheSize() > nCoinCacheSize) ||
            (mode == FLUSH_STATE_PERIODIC && GetTimeMicros() > nLastWrite + DATABASE_WRITE_INTERVAL * 1000000)) {
            // Typical CCoins structures on disk are around 100 bytes in size.
            // Pushing a new one to the database can cause it to be written
            // twice (once in the log, and once in the tables). This is already
            // an overestimation, as most will delete an existing entry or
            // overwrite one. Still, use a conservative safety factor of 2.
            if (!CheckDiskSpace(100 * 2 * 2 * pcoinsTip->GetCacheSize()))
                return state.Error("out of disk space");
            // First make sure all block and undo data is flushed to disk.
            FlushBlockFile();
            // Then update all block file information (which may refer to block and undo files).
            bool fileschanged = false;
            for (set<int>::iterator it = setDirtyFileInfo.begin(); it != setDirtyFileInfo.end();) {
                if (!pblocktree->WriteBlockFileInfo(*it, vinfoBlockFile[*it])) {
                    return state.Abort("Failed to write to block index");
                }
                fileschanged = true;
                setDirtyFileInfo.erase(it++);
            }
            if (fileschanged && !pblocktree->WriteLastBlockFile(nLastBlockFile)) {
                return state.Abort("Failed to write to block index");
            }
            for (set<CBlockIndex*>::iterator it = setDirtyBlockIndex.begin(); it != setDirtyBlockIndex.end();) {
                if (!pblocktree->WriteBlockIndex(CDiskBlockIndex(*it))) {
                    return state.Abort("Failed to write to block index");
                }
                setDirtyBlockIndex.erase(it++);
            }
            pblocktree->Sync();
            // Finally flush the chainstate (which may refer to block index entries).
            if (!pcoinsTip->Flush())
                return state.Abort("Failed to write to coin database");
            // Update best block in wallet (so we can detect restored wallets).
            if (mode != FLUSH_STATE_IF_NEEDED) {
                g_signals.SetBestChain(chainActive.GetLocator());
            }
            nLastWrite = GetTimeMicros();
        }
    } catch (const std::runtime_error& e) {
        return state.Abort(std::string("System error while flushing: ") + e.what());
    }
    return true;
}

void FlushStateToDisk()
{
    CValidationState state;
    FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
}

/** Update chainActive and related internal data structures. */
void static UpdateTip(CBlockIndex* pindexNew)
{
    chainActive.SetTip(pindexNew);

    // New best block
    nTimeBestReceived = GetTime();
    mempool.AddTransactionsUpdated(1);

    LogPrintf("UpdateTip: new best=%s  height=%d  log2_work=%.8g  tx=%lu  date=%s progress=%f  cache=%u\n",
        chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(), log(chainActive.Tip()->nChainWork.getdouble()) / log(2.0), (unsigned long)chainActive.Tip()->nChainTx,
        DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
        Checkpoints::GuessVerificationProgress(chainActive.Tip()), (unsigned int)pcoinsTip->GetCacheSize());

    cvBlockChange.notify_all();

    // Check the version of the last 100 blocks to see if we need to upgrade:
    static bool fWarned = false;
    if (!IsInitialBlockDownload() && !fWarned) {
        int nUpgraded = 0;
        const CBlockIndex* pindex = chainActive.Tip();
        for (int i = 0; i < 100 && pindex != NULL; i++) {
            if (pindex->nVersion > CBlock::CURRENT_VERSION)
                ++nUpgraded;
            pindex = pindex->pprev;
        }
        if (nUpgraded > 0)
            LogPrintf("SetBestChain: %d of last 100 blocks above version %d\n", nUpgraded, (int)CBlock::CURRENT_VERSION);
        if (nUpgraded > 100 / 2) {
            // strMiscWarning is read by GetWarnings(), called by Qt and the JSON-RPC code to warn the user:
            strMiscWarning = _("Warning: This version is obsolete, upgrade required!");
            CAlert::Notify(strMiscWarning, true);
            fWarned = true;
        }
    }
}

/** Disconnect chainActive's tip. */
bool static DisconnectTip(CValidationState& state)
{
    CBlockIndex* pindexDelete = chainActive.Tip();
    assert(pindexDelete);
    mempool.check(pcoinsTip);
    // Read block from disk.
    CBlock block;
    if (!ReadBlockFromDisk(block, pindexDelete))
        return state.Abort("Failed to read block");
    // Apply the block atomically to the chain state.
    int64_t nStart = GetTimeMicros();
    {
        CCoinsViewCache view(pcoinsTip);
        if (!DisconnectBlock(block, state, pindexDelete, view))
            return error("DisconnectTip() : DisconnectBlock %s failed", pindexDelete->GetBlockHash().ToString());
        assert(view.Flush());
    }
    LogPrint("bench", "- Disconnect block: %.2fms\n", (GetTimeMicros() - nStart) * 0.001);
    // Write the chain state to disk, if necessary.
    if (!FlushStateToDisk(state, FLUSH_STATE_ALWAYS))
        return false;
    // Resurrect mempool transactions from the disconnected block.
    BOOST_FOREACH (const CTransaction& tx, block.vtx) {
        // ignore validation errors in resurrected transactions
        list<CTransaction> removed;
        CValidationState stateDummy;
        if (tx.IsCoinBase() || tx.IsCoinStake() || !AcceptToMemoryPool(mempool, stateDummy, tx, false, NULL))
            mempool.remove(tx, removed, true);
    }
    mempool.removeCoinbaseSpends(pcoinsTip, pindexDelete->nHeight);
    mempool.check(pcoinsTip);
    // Update chainActive and related variables.
    UpdateTip(pindexDelete->pprev);
    // Let wallets know transactions went from 1-confirmed to
    // 0-confirmed or conflicted:
    BOOST_FOREACH (const CTransaction& tx, block.vtx) {
        SyncWithWallets(tx, NULL);
    }
    return true;
}

static int64_t nTimeReadFromDisk = 0;
static int64_t nTimeConnectTotal = 0;
static int64_t nTimeFlush = 0;
static int64_t nTimeChainState = 0;
static int64_t nTimePostConnect = 0;

/**
 * Connect a new block to chainActive. pblock is either NULL or a pointer to a CBlock
 * corresponding to pindexNew, to bypass loading it again from disk.
 */
bool static ConnectTip(CValidationState& state, CBlockIndex* pindexNew, CBlock* pblock)
{
    assert(pindexNew->pprev == chainActive.Tip());
    mempool.check(pcoinsTip);
    CCoinsViewCache view(pcoinsTip);

    // Read block from disk.
    int64_t nTime1 = GetTimeMicros();
    CBlock block;
    if (!pblock) {
        if (!ReadBlockFromDisk(block, pindexNew))
            return state.Abort("Failed to read block");
        pblock = &block;
    }
    // Apply the block atomically to the chain state.
    int64_t nTime2 = GetTimeMicros();
    nTimeReadFromDisk += nTime2 - nTime1;
    int64_t nTime3;
    LogPrint("bench", "  - Load block from disk: %.2fms [%.2fs]\n", (nTime2 - nTime1) * 0.001, nTimeReadFromDisk * 0.000001);
    {
        CInv inv(MSG_BLOCK, pindexNew->GetBlockHash());
        bool rv = ConnectBlock(*pblock, state, pindexNew, view);
        g_signals.BlockChecked(*pblock, state);
        if (!rv) {
            if (state.IsInvalid())
                InvalidBlockFound(pindexNew, state);
            return error("ConnectTip() : ConnectBlock %s failed", pindexNew->GetBlockHash().ToString());
        }
        mapBlockSource.erase(inv.hash);
        nTime3 = GetTimeMicros();
        nTimeConnectTotal += nTime3 - nTime2;
        LogPrint("bench", "  - Connect total: %.2fms [%.2fs]\n", (nTime3 - nTime2) * 0.001, nTimeConnectTotal * 0.000001);
        assert(view.Flush());
    }
    int64_t nTime4 = GetTimeMicros();
    nTimeFlush += nTime4 - nTime3;
    LogPrint("bench", "  - Flush: %.2fms [%.2fs]\n", (nTime4 - nTime3) * 0.001, nTimeFlush * 0.000001);

    // Write the chain state to disk, if necessary. Always write to disk if this is the first of a new file.
    FlushStateMode flushMode = FLUSH_STATE_IF_NEEDED;
    if (pindexNew->pprev && (pindexNew->GetBlockPos().nFile != pindexNew->pprev->GetBlockPos().nFile))
        flushMode = FLUSH_STATE_ALWAYS;
    if (!FlushStateToDisk(state, flushMode))
        return false;
    int64_t nTime5 = GetTimeMicros();
    nTimeChainState += nTime5 - nTime4;
    LogPrint("bench", "  - Writing chainstate: %.2fms [%.2fs]\n", (nTime5 - nTime4) * 0.001, nTimeChainState * 0.000001);

    // Remove conflicting transactions from the mempool.
    list<CTransaction> txConflicted;
    mempool.removeForBlock(pblock->vtx, pindexNew->nHeight, txConflicted);
    mempool.check(pcoinsTip);
    // Update chainActive & related variables.
    UpdateTip(pindexNew);
    // Tell wallet about transactions that went from mempool
    // to conflicted:
    BOOST_FOREACH (const CTransaction& tx, txConflicted) {
        SyncWithWallets(tx, NULL);
    }
    // ... and about transactions that got confirmed:
    BOOST_FOREACH (const CTransaction& tx, pblock->vtx) {
        SyncWithWallets(tx, pblock);
    }

    int64_t nTime6 = GetTimeMicros();
    nTimePostConnect += nTime6 - nTime5;
    nTimeTotal += nTime6 - nTime1;
    LogPrint("bench", "  - Connect postprocess: %.2fms [%.2fs]\n", (nTime6 - nTime5) * 0.001, nTimePostConnect * 0.000001);
    LogPrint("bench", "- Connect block: %.2fms [%.2fs]\n", (nTime6 - nTime1) * 0.001, nTimeTotal * 0.000001);
    return true;
}

bool DisconnectBlocksAndReprocess(int blocks)
{
    LOCK(cs_main);

    CValidationState state;

    LogPrintf("DisconnectBlocksAndReprocess: Got command to replay %d blocks\n", blocks);
    for (int i = 0; i <= blocks; i++)
        DisconnectTip(state);

    return true;
}

/*
    DisconnectBlockAndInputs

    Remove conflicting blocks for successful SwiftTX transaction locks
    This should be very rare (Probably will never happen)
*/
// ***TODO*** clean up here
bool DisconnectBlockAndInputs(CValidationState& state, CTransaction txLock)
{
    // All modifications to the coin state will be done in this cache.
    // Only when all have succeeded, we push it to pcoinsTip.
    //    CCoinsViewCache view(*pcoinsTip, true);

    CBlockIndex* BlockReading = chainActive.Tip();
    CBlockIndex* pindexNew = NULL;

    bool foundConflictingTx = false;

    //remove anything conflicting in the memory pool
    list<CTransaction> txConflicted;
    mempool.removeConflicts(txLock, txConflicted);


    // List of what to disconnect (typically nothing)
    vector<CBlockIndex*> vDisconnect;

    for (unsigned int i = 1; BlockReading && BlockReading->nHeight > 0 && !foundConflictingTx && i < 6; i++) {
        vDisconnect.push_back(BlockReading);
        pindexNew = BlockReading->pprev; //new best block

        CBlock block;
        if (!ReadBlockFromDisk(block, BlockReading))
            return state.Abort(_("Failed to read block"));

        // Queue memory transactions to resurrect.
        // We only do this for blocks after the last checkpoint (reorganisation before that
        // point should only happen with -reindex/-loadblock, or a misbehaving peer.
        BOOST_FOREACH (const CTransaction& tx, block.vtx) {
            if (!tx.IsCoinBase()) {
                BOOST_FOREACH (const CTxIn& in1, txLock.vin) {
                    BOOST_FOREACH (const CTxIn& in2, tx.vin) {
                        if (in1.prevout == in2.prevout) foundConflictingTx = true;
                    }
                }
            }
        }

        if (BlockReading->pprev == NULL) {
            assert(BlockReading);
            break;
        }
        BlockReading = BlockReading->pprev;
    }

    if (!foundConflictingTx) {
        LogPrintf("DisconnectBlockAndInputs: Can't find a conflicting transaction to inputs\n");
        return false;
    }

    if (vDisconnect.size() > 0) {
        LogPrintf("REORGANIZE: Disconnect Conflicting Blocks %lli blocks; %s..\n", vDisconnect.size(), pindexNew->GetBlockHash().ToString());
        BOOST_FOREACH (CBlockIndex* pindex, vDisconnect) {
            LogPrintf(" -- disconnect %s\n", pindex->GetBlockHash().ToString());
            DisconnectTip(state);
        }
    }

    return true;
}


/**
 * Return the tip of the chain with the most work in it, that isn't
 * known to be invalid (it's however far from certain to be valid).
 */
static CBlockIndex* FindMostWorkChain()
{
    do {
        CBlockIndex* pindexNew = NULL;

        // Find the best candidate header.
        {
            std::set<CBlockIndex*, CBlockIndexWorkComparator>::reverse_iterator it = setBlockIndexCandidates.rbegin();
            if (it == setBlockIndexCandidates.rend())
                return NULL;
            pindexNew = *it;
        }

        // Check whether all blocks on the path between the currently active chain and the candidate are valid.
        // Just going until the active chain is an optimization, as we know all blocks in it are valid already.
        CBlockIndex* pindexTest = pindexNew;
        bool fInvalidAncestor = false;
        while (pindexTest && !chainActive.Contains(pindexTest)) {
            assert(pindexTest->nChainTx || pindexTest->nHeight == 0);

            // Pruned nodes may have entries in setBlockIndexCandidates for
            // which block files have been deleted.  Remove those as candidates
            // for the most work chain if we come across them; we can't switch
            // to a chain unless we have all the non-active-chain parent blocks.
            bool fFailedChain = pindexTest->nStatus & BLOCK_FAILED_MASK;
            bool fMissingData = !(pindexTest->nStatus & BLOCK_HAVE_DATA);
            if (fFailedChain || fMissingData) {
                // Candidate chain is not usable (either invalid or missing data)
                if (fFailedChain && (pindexBestInvalid == NULL || pindexNew->nChainWork > pindexBestInvalid->nChainWork))
                    pindexBestInvalid = pindexNew;
                CBlockIndex* pindexFailed = pindexNew;
                // Remove the entire chain from the set.
                while (pindexTest != pindexFailed) {
                    if (fFailedChain) {
                        pindexFailed->nStatus |= BLOCK_FAILED_CHILD;
                    } else if (fMissingData) {
                        // If we're missing data, then add back to mapBlocksUnlinked,
                        // so that if the block arrives in the future we can try adding
                        // to setBlockIndexCandidates again.
                        mapBlocksUnlinked.insert(std::make_pair(pindexFailed->pprev, pindexFailed));
                    }
                    setBlockIndexCandidates.erase(pindexFailed);
                    pindexFailed = pindexFailed->pprev;
                }
                setBlockIndexCandidates.erase(pindexTest);
                fInvalidAncestor = true;
                break;
            }
            pindexTest = pindexTest->pprev;
        }
        if (!fInvalidAncestor)
            return pindexNew;
    } while (true);
}

/** Delete all entries in setBlockIndexCandidates that are worse than the current tip. */
static void PruneBlockIndexCandidates()
{
    // Note that we can't delete the current block itself, as we may need to return to it later in case a
    // reorganization to a better block fails.
    std::set<CBlockIndex*, CBlockIndexWorkComparator>::iterator it = setBlockIndexCandidates.begin();
    while (it != setBlockIndexCandidates.end() && setBlockIndexCandidates.value_comp()(*it, chainActive.Tip())) {
        setBlockIndexCandidates.erase(it++);
    }
    // Either the current tip or a successor of it we're working towards is left in setBlockIndexCandidates.
    assert(!setBlockIndexCandidates.empty());
}

/**
 * Try to make some progress towards making pindexMostWork the active block.
 * pblock is either NULL or a pointer to a CBlock corresponding to pindexMostWork.
 */
static bool ActivateBestChainStep(CValidationState& state, CBlockIndex* pindexMostWork, CBlock* pblock)
{
    AssertLockHeld(cs_main);
    bool fInvalidFound = false;
    const CBlockIndex* pindexOldTip = chainActive.Tip();
    const CBlockIndex* pindexFork = chainActive.FindFork(pindexMostWork);

    // Disconnect active blocks which are no longer in the best chain.
    while (chainActive.Tip() && chainActive.Tip() != pindexFork) {
        if (!DisconnectTip(state))
            return false;
    }

    // Build list of new blocks to connect.
    std::vector<CBlockIndex*> vpindexToConnect;
    bool fContinue = true;
    int nHeight = pindexFork ? pindexFork->nHeight : -1;
    while (fContinue && nHeight != pindexMostWork->nHeight) {
        // Don't iterate the entire list of potential improvements toward the best tip, as we likely only need
        // a few blocks along the way.
        int nTargetHeight = std::min(nHeight + 32, pindexMostWork->nHeight);
        vpindexToConnect.clear();
        vpindexToConnect.reserve(nTargetHeight - nHeight);
        CBlockIndex* pindexIter = pindexMostWork->GetAncestor(nTargetHeight);
        while (pindexIter && pindexIter->nHeight != nHeight) {
            vpindexToConnect.push_back(pindexIter);
            pindexIter = pindexIter->pprev;
        }
        nHeight = nTargetHeight;

        // Connect new blocks.
        BOOST_REVERSE_FOREACH (CBlockIndex* pindexConnect, vpindexToConnect) {
            if (!ConnectTip(state, pindexConnect, pindexConnect == pindexMostWork ? pblock : NULL)) {
                if (state.IsInvalid()) {
                    // The block violates a consensus rule.
                    if (!state.CorruptionPossible())
                        InvalidChainFound(vpindexToConnect.back());
                    state = CValidationState();
                    fInvalidFound = true;
                    fContinue = false;
                    break;
                } else {
                    // A system error occurred (disk space, database error, ...).
                    return false;
                }
            } else {
                PruneBlockIndexCandidates();
                if (!pindexOldTip || chainActive.Tip()->nChainWork > pindexOldTip->nChainWork) {
                    // We're in a better position than we were. Return temporarily to release the lock.
                    fContinue = false;
                    break;
                }
            }
        }
    }

    // Callbacks/notifications for a new best chain.
    if (fInvalidFound)
        CheckForkWarningConditionsOnNewFork(vpindexToConnect.back());
    else
        CheckForkWarningConditions();

    return true;
}

/**
 * Make the best chain active, in multiple steps. The result is either failure
 * or an activated best chain. pblock is either NULL or a pointer to a block
 * that is already loaded (to avoid loading it again from disk).
 */
bool ActivateBestChain(CValidationState& state, CBlock* pblock)
{
    CBlockIndex* pindexNewTip = NULL;
    CBlockIndex* pindexMostWork = NULL;
    do {
        boost::this_thread::interruption_point();

        bool fInitialDownload;
        while (true) {
            TRY_LOCK(cs_main, lockMain);
            if (!lockMain) {
                MilliSleep(50);
                continue;
            }

            pindexMostWork = FindMostWorkChain();

            // Whether we have anything to do at all.
            if (pindexMostWork == NULL || pindexMostWork == chainActive.Tip())
                return true;

            if (!ActivateBestChainStep(state, pindexMostWork, pblock && pblock->GetHash() == pindexMostWork->GetBlockHash() ? pblock : NULL))
                return false;

            pindexNewTip = chainActive.Tip();
            fInitialDownload = IsInitialBlockDownload();
            break;
        }
        // When we reach this point, we switched to a new tip (stored in pindexNewTip).

        // Notifications/callbacks that can run without cs_main
        if (!fInitialDownload) {
            uint256 hashNewTip = pindexNewTip->GetBlockHash();
            // Relay inventory, but don't relay old inventory during initial block download.
            int nBlockEstimate = Checkpoints::GetTotalBlocksEstimate();
            {
                LOCK(cs_vNodes);
                BOOST_FOREACH (CNode* pnode, vNodes)
                    if (chainActive.Height() > (pnode->nStartingHeight != -1 ? pnode->nStartingHeight - 2000 : nBlockEstimate))
                        pnode->PushInventory(CInv(MSG_BLOCK, hashNewTip));
            }
            // Notify external listeners about the new tip.
            uiInterface.NotifyBlockTip(hashNewTip);
        }
    } while (pindexMostWork != chainActive.Tip());
    CheckBlockIndex();

    // Write changes periodically to disk, after relay.
    if (!FlushStateToDisk(state, FLUSH_STATE_PERIODIC)) {
        return false;
    }

    return true;
}

bool InvalidateBlock(CValidationState& state, CBlockIndex* pindex)
{
    AssertLockHeld(cs_main);

    // Mark the block itself as invalid.
    pindex->nStatus |= BLOCK_FAILED_VALID;
    setDirtyBlockIndex.insert(pindex);
    setBlockIndexCandidates.erase(pindex);

    while (chainActive.Contains(pindex)) {
        CBlockIndex* pindexWalk = chainActive.Tip();
        pindexWalk->nStatus |= BLOCK_FAILED_CHILD;
        setDirtyBlockIndex.insert(pindexWalk);
        setBlockIndexCandidates.erase(pindexWalk);
        // ActivateBestChain considers blocks already in chainActive
        // unconditionally valid already, so force disconnect away from it.
        if (!DisconnectTip(state)) {
            return false;
        }
    }

    // The resulting new best tip may not be in setBlockIndexCandidates anymore, so
    // add them again.
    BlockMap::iterator it = mapBlockIndex.begin();
    while (it != mapBlockIndex.end()) {
        if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && !setBlockIndexCandidates.value_comp()(it->second, chainActive.Tip())) {
            setBlockIndexCandidates.insert(it->second);
        }
        it++;
    }

    InvalidChainFound(pindex);
    return true;
}

bool ReconsiderBlock(CValidationState& state, CBlockIndex* pindex)
{
    AssertLockHeld(cs_main);

    int nHeight = pindex->nHeight;

    // Remove the invalidity flag from this block and all its descendants.
    BlockMap::iterator it = mapBlockIndex.begin();
    while (it != mapBlockIndex.end()) {
        if (!it->second->IsValid() && it->second->GetAncestor(nHeight) == pindex) {
            it->second->nStatus &= ~BLOCK_FAILED_MASK;
            setDirtyBlockIndex.insert(it->second);
            if (it->second->IsValid(BLOCK_VALID_TRANSACTIONS) && it->second->nChainTx && setBlockIndexCandidates.value_comp()(chainActive.Tip(), it->second)) {
                setBlockIndexCandidates.insert(it->second);
            }
            if (it->second == pindexBestInvalid) {
                // Reset invalid block marker if it was pointing to one of those.
                pindexBestInvalid = NULL;
            }
        }
        it++;
    }

    // Remove the invalidity flag from all ancestors too.
    while (pindex != NULL) {
        if (pindex->nStatus & BLOCK_FAILED_MASK) {
            pindex->nStatus &= ~BLOCK_FAILED_MASK;
            setDirtyBlockIndex.insert(pindex);
        }
        pindex = pindex->pprev;
    }
    return true;
}

CBlockIndex* AddToBlockIndex(const CBlock& block)
{
    // Check for duplicate
    uint256 hash = block.GetHash();
    BlockMap::iterator it = mapBlockIndex.find(hash);
    if (it != mapBlockIndex.end())
        return it->second;

    // Construct new block index object
    CBlockIndex* pindexNew = new CBlockIndex(block);
    assert(pindexNew);
    // We assign the sequence id to blocks only when the full data is available,
    // to avoid miners withholding blocks but broadcasting headers, to get a
    // competitive advantage.
    pindexNew->nSequenceId = 0;
    BlockMap::iterator mi = mapBlockIndex.insert(make_pair(hash, pindexNew)).first;

    //mark as PoS seen
    if (pindexNew->IsProofOfStake())
        setStakeSeen.insert(make_pair(pindexNew->prevoutStake, pindexNew->nStakeTime));

    pindexNew->phashBlock = &((*mi).first);
    BlockMap::iterator miPrev = mapBlockIndex.find(block.hashPrevBlock);
    if (miPrev != mapBlockIndex.end()) {
        pindexNew->pprev = (*miPrev).second;
        pindexNew->nHeight = pindexNew->pprev->nHeight + 1;
        pindexNew->BuildSkip();

        //update previous block pointer
        pindexNew->pprev->pnext = pindexNew;

        // ppcoin: compute chain trust score
        pindexNew->bnChainTrust = (pindexNew->pprev ? pindexNew->pprev->bnChainTrust : 0) + pindexNew->GetBlockTrust();

        // ppcoin: compute stake entropy bit for stake modifier
        if (!pindexNew->SetStakeEntropyBit(pindexNew->GetStakeEntropyBit()))
            LogPrintf("AddToBlockIndex() : SetStakeEntropyBit() failed \n");

        // ppcoin: record proof-of-stake hash value
        if (pindexNew->IsProofOfStake()) {
            if (!mapProofOfStake.count(hash))
                LogPrintf("AddToBlockIndex() : hashProofOfStake not found in map \n");
            pindexNew->hashProofOfStake = mapProofOfStake[hash];
        }

        // ppcoin: compute stake modifier
        uint64_t nStakeModifier = 0;
        bool fGeneratedStakeModifier = false;
        if (!ComputeNextStakeModifier(pindexNew->pprev, nStakeModifier, fGeneratedStakeModifier))
            LogPrintf("AddToBlockIndex() : ComputeNextStakeModifier() failed \n");
        pindexNew->SetStakeModifier(nStakeModifier, fGeneratedStakeModifier);
        pindexNew->nStakeModifierChecksum = GetStakeModifierChecksum(pindexNew);
        if (!CheckStakeModifierCheckpoints(pindexNew->nHeight, pindexNew->nStakeModifierChecksum))
            LogPrintf("AddToBlockIndex() : Rejected by stake modifier checkpoint height=%d, modifier=%s \n", pindexNew->nHeight, boost::lexical_cast<std::string>(nStakeModifier));
    }
    pindexNew->nChainWork = (pindexNew->pprev ? pindexNew->pprev->nChainWork : 0) + GetBlockProof(*pindexNew);
    pindexNew->RaiseValidity(BLOCK_VALID_TREE);
    if (pindexBestHeader == NULL || pindexBestHeader->nChainWork < pindexNew->nChainWork)
        pindexBestHeader = pindexNew;

    //update previous block pointer
    if (pindexNew->nHeight)
        pindexNew->pprev->pnext = pindexNew;

    setDirtyBlockIndex.insert(pindexNew);

    return pindexNew;
}

/** Mark a block as having its data received and checked (up to BLOCK_VALID_TRANSACTIONS). */
bool ReceivedBlockTransactions(const CBlock& block, CValidationState& state, CBlockIndex* pindexNew, const CDiskBlockPos& pos)
{
    if (block.IsProofOfStake())
        pindexNew->SetProofOfStake();
    pindexNew->nTx = block.vtx.size();
    pindexNew->nChainTx = 0;
    pindexNew->nFile = pos.nFile;
    pindexNew->nDataPos = pos.nPos;
    pindexNew->nUndoPos = 0;
    pindexNew->nStatus |= BLOCK_HAVE_DATA;
    pindexNew->RaiseValidity(BLOCK_VALID_TRANSACTIONS);
    setDirtyBlockIndex.insert(pindexNew);

    if (pindexNew->pprev == NULL || pindexNew->pprev->nChainTx) {
        // If pindexNew is the genesis block or all parents are BLOCK_VALID_TRANSACTIONS.
        deque<CBlockIndex*> queue;
        queue.push_back(pindexNew);

        // Recursively process any descendant blocks that now may be eligible to be connected.
        while (!queue.empty()) {
            CBlockIndex* pindex = queue.front();
            queue.pop_front();
            pindex->nChainTx = (pindex->pprev ? pindex->pprev->nChainTx : 0) + pindex->nTx;
            {
                LOCK(cs_nBlockSequenceId);
                pindex->nSequenceId = nBlockSequenceId++;
            }
            if (chainActive.Tip() == NULL || !setBlockIndexCandidates.value_comp()(pindex, chainActive.Tip())) {
                setBlockIndexCandidates.insert(pindex);
            }
            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = mapBlocksUnlinked.equal_range(pindex);
            while (range.first != range.second) {
                std::multimap<CBlockIndex*, CBlockIndex*>::iterator it = range.first;
                queue.push_back(it->second);
                range.first++;
                mapBlocksUnlinked.erase(it);
            }
        }
    } else {
        if (pindexNew->pprev && pindexNew->pprev->IsValid(BLOCK_VALID_TREE)) {
            mapBlocksUnlinked.insert(std::make_pair(pindexNew->pprev, pindexNew));
        }
    }

    return true;
}

bool FindBlockPos(CValidationState& state, CDiskBlockPos& pos, unsigned int nAddSize, unsigned int nHeight, uint64_t nTime, bool fKnown = false)
{
    LOCK(cs_LastBlockFile);

    unsigned int nFile = fKnown ? pos.nFile : nLastBlockFile;
    if (vinfoBlockFile.size() <= nFile) {
        vinfoBlockFile.resize(nFile + 1);
    }

    if (!fKnown) {
        while (vinfoBlockFile[nFile].nSize + nAddSize >= MAX_BLOCKFILE_SIZE) {
            LogPrintf("Leaving block file %i: %s\n", nFile, vinfoBlockFile[nFile].ToString());
            FlushBlockFile(true);
            nFile++;
            if (vinfoBlockFile.size() <= nFile) {
                vinfoBlockFile.resize(nFile + 1);
            }
        }
        pos.nFile = nFile;
        pos.nPos = vinfoBlockFile[nFile].nSize;
    }

    nLastBlockFile = nFile;
    vinfoBlockFile[nFile].AddBlock(nHeight, nTime);
    if (fKnown)
        vinfoBlockFile[nFile].nSize = std::max(pos.nPos + nAddSize, vinfoBlockFile[nFile].nSize);
    else
        vinfoBlockFile[nFile].nSize += nAddSize;

    if (!fKnown) {
        unsigned int nOldChunks = (pos.nPos + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
        unsigned int nNewChunks = (vinfoBlockFile[nFile].nSize + BLOCKFILE_CHUNK_SIZE - 1) / BLOCKFILE_CHUNK_SIZE;
        if (nNewChunks > nOldChunks) {
            if (CheckDiskSpace(nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos)) {
                FILE* file = OpenBlockFile(pos);
                if (file) {
                    LogPrintf("Pre-allocating up to position 0x%x in blk%05u.dat\n", nNewChunks * BLOCKFILE_CHUNK_SIZE, pos.nFile);
                    AllocateFileRange(file, pos.nPos, nNewChunks * BLOCKFILE_CHUNK_SIZE - pos.nPos);
                    fclose(file);
                }
            } else
                return state.Error("out of disk space");
        }
    }

    setDirtyFileInfo.insert(nFile);
    return true;
}

bool FindUndoPos(CValidationState& state, int nFile, CDiskBlockPos& pos, unsigned int nAddSize)
{
    pos.nFile = nFile;

    LOCK(cs_LastBlockFile);

    unsigned int nNewSize;
    pos.nPos = vinfoBlockFile[nFile].nUndoSize;
    nNewSize = vinfoBlockFile[nFile].nUndoSize += nAddSize;
    setDirtyFileInfo.insert(nFile);

    unsigned int nOldChunks = (pos.nPos + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
    unsigned int nNewChunks = (nNewSize + UNDOFILE_CHUNK_SIZE - 1) / UNDOFILE_CHUNK_SIZE;
    if (nNewChunks > nOldChunks) {
        if (CheckDiskSpace(nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos)) {
            FILE* file = OpenUndoFile(pos);
            if (file) {
                LogPrintf("Pre-allocating up to position 0x%x in rev%05u.dat\n", nNewChunks * UNDOFILE_CHUNK_SIZE, pos.nFile);
                AllocateFileRange(file, pos.nPos, nNewChunks * UNDOFILE_CHUNK_SIZE - pos.nPos);
                fclose(file);
            }
        } else
            return state.Error("out of disk space");
    }

    return true;
}

bool CheckBlockHeader(const CBlockHeader& block, CValidationState& state, bool fCheckPOW)
{
    // Check proof of work matches claimed amount
    if (fCheckPOW && !CheckProofOfWork(block.GetHash(), block.nBits))
        return state.DoS(50, error("CheckBlockHeader() : proof of work failed"),
            REJECT_INVALID, "high-hash");

    return true;
}

bool CheckBlock(const CBlock& block, CValidationState& state, bool fCheckPOW, bool fCheckMerkleRoot, bool fCheckSig)
{
    // These are checks that are independent of context.

    // Check that the header is valid (particularly PoW).  This is mostly
    // redundant with the call in AcceptBlockHeader.
    if (!CheckBlockHeader(block, state, block.IsProofOfWork()))
        return state.DoS(100, error("CheckBlock() : CheckBlockHeader failed"),
            REJECT_INVALID, "bad-header", true);

    // Check timestamp
    LogPrint("debug", "%s: block=%s  is proof of stake=%d\n", __func__, block.GetHash().ToString().c_str(), block.IsProofOfStake());
    if (block.GetBlockTime() > GetAdjustedTime() + (block.IsProofOfStake() ? 180 : 7200)) // 3 minute future drift for PoS
        return state.Invalid(error("CheckBlock() : block timestamp too far in the future"),
            REJECT_INVALID, "time-too-new");


    // Check the merkle root.
    if (fCheckMerkleRoot) {
        bool mutated;
        uint256 hashMerkleRoot2 = block.BuildMerkleTree(&mutated);
        if (block.hashMerkleRoot != hashMerkleRoot2)
            return state.DoS(100, error("CheckBlock() : hashMerkleRoot mismatch"),
                REJECT_INVALID, "bad-txnmrklroot", true);

        // Check for merkle tree malleability (CVE-2012-2459): repeating sequences
        // of transactions in a block without affecting the merkle root of a block,
        // while still invalidating it.
        if (mutated)
            return state.DoS(100, error("CheckBlock() : duplicate transaction"),
                REJECT_INVALID, "bad-txns-duplicate", true);
    }

    // All potential-corruption validation must be done before we do any
    // transaction validation, as otherwise we may mark the header as invalid
    // because we receive the wrong transactions for it.

    // Size limits
    if (block.vtx.empty() || block.vtx.size() > MAX_BLOCK_SIZE || ::GetSerializeSize(block, SER_NETWORK, PROTOCOL_VERSION) > MAX_BLOCK_SIZE)
        return state.DoS(100, error("CheckBlock() : size limits failed"),
            REJECT_INVALID, "bad-blk-length");

    // First transaction must be coinbase, the rest must not be
    if (block.vtx.empty() || !block.vtx[0].IsCoinBase())
        return state.DoS(100, error("CheckBlock() : first tx is not coinbase"),
            REJECT_INVALID, "bad-cb-missing");
    for (unsigned int i = 1; i < block.vtx.size(); i++)
        if (block.vtx[i].IsCoinBase())
            return state.DoS(100, error("CheckBlock() : more than one coinbase"),
                REJECT_INVALID, "bad-cb-multiple");

    if (block.IsProofOfStake()) {
        // Coinbase output should be empty if proof-of-stake block
        if (block.vtx[0].vout.size() != 1 || !block.vtx[0].vout[0].IsEmpty())
            return state.DoS(100, error("CheckBlock() : coinbase output not empty for proof-of-stake block"));

        // Second transaction must be coinstake, the rest must not be
        if (block.vtx.empty() || !block.vtx[1].IsCoinStake())
            return state.DoS(100, error("CheckBlock() : second tx is not coinstake"));
        for (unsigned int i = 2; i < block.vtx.size(); i++)
            if (block.vtx[i].IsCoinStake())
                return state.DoS(100, error("CheckBlock() : more than one coinstake"));
    }

    // ----------- swiftTX transaction scanning -----------

    if (IsSporkActive(SPORK_3_SWIFTTX_BLOCK_FILTERING)) {
        BOOST_FOREACH (const CTransaction& tx, block.vtx) {
            if (!tx.IsCoinBase()) {
                //only reject blocks when it's based on complete consensus
                BOOST_FOREACH (const CTxIn& in, tx.vin) {
                    if (mapLockedInputs.count(in.prevout)) {
                        if (mapLockedInputs[in.prevout] != tx.GetHash()) {
                            mapRejectedBlocks.insert(make_pair(block.GetHash(), GetTime()));
                            LogPrintf("CheckBlock() : found conflicting transaction with transaction lock %s %s\n", mapLockedInputs[in.prevout].ToString(), tx.GetHash().ToString());
                            return state.DoS(0, error("CheckBlock() : found conflicting transaction with transaction lock"),
                                REJECT_INVALID, "conflicting-tx-ix");
                        }
                    }
                }
            }
        }
    } else {
        LogPrintf("CheckBlock() : skipping transaction locking checks\n");
    }


    // ----------- masternode payments / budgets -----------

    CBlockIndex* pindexPrev = chainActive.Tip();
    if (pindexPrev != NULL) {
        int nHeight = 0;
        if (pindexPrev->GetBlockHash() == block.hashPrevBlock) {
            nHeight = pindexPrev->nHeight + 1;
        } else { //out of order
            BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
            if (mi != mapBlockIndex.end() && (*mi).second)
                nHeight = (*mi).second->nHeight + 1;
        }

        // Altbet
        // It is entierly possible that we don't have enough data and this could fail
        // (i.e. the block could indeed be valid). Store the block for later consideration
        // but issue an initial reject message.
        // The case also exists that the sending peer could not have enough data to see
        // that this block is invalid, so don't issue an outright ban.
        if (nHeight != 0 && !IsInitialBlockDownload()) {
            if (!IsBlockPayeeValid(block, nHeight)) {
                mapRejectedBlocks.insert(make_pair(block.GetHash(), GetTime()));
                return state.DoS(0, error("CheckBlock() : Couldn't find masternode/budget payment"),
                        REJECT_INVALID, "bad-cb-payee");
            }
        } else {
            if (fDebug)
                LogPrintf("CheckBlock(): Masternode payment check skipped on sync - skipping IsBlockPayeeValid()\n");
        }
    }

    // -------------------------------------------

    // Check transactions
    BOOST_FOREACH (const CTransaction& tx, block.vtx)
        if (!CheckTransaction(tx, state))
            return error("CheckBlock() : CheckTransaction failed");

    unsigned int nSigOps = 0;
    BOOST_FOREACH (const CTransaction& tx, block.vtx) {
        nSigOps += GetLegacySigOpCount(tx);
    }
    if (nSigOps > MAX_BLOCK_SIGOPS)
        return state.DoS(100, error("CheckBlock() : out-of-bounds SigOpCount"),
            REJECT_INVALID, "bad-blk-sigops", true);

    return true;
}

bool CheckWork(const CBlock block, CBlockIndex* const pindexPrev)
{
    if (pindexPrev == NULL)
        return error("%s : null pindexPrev for block %s", __func__, block.GetHash().ToString().c_str());

    unsigned int nBitsRequired = GetNextWorkRequired(pindexPrev, &block);

    if (block.IsProofOfWork() && (pindexPrev->nHeight + 1 <= 68589)) {
        double n1 = ConvertBitsToDouble(block.nBits);
        double n2 = ConvertBitsToDouble(nBitsRequired);

        if (abs(n1 - n2) > n1 * 0.5)
            return error("%s : incorrect proof of work (DGW pre-fork) - %f %f %f at %d", __func__, abs(n1 - n2), n1, n2, pindexPrev->nHeight + 1);

        return true;
    }

    if (block.nBits != nBitsRequired)
        return error("%s : incorrect proof of work at %d", __func__, pindexPrev->nHeight + 1);

    if (block.IsProofOfStake()) {
        uint256 hashProofOfStake;
        uint256 hash = block.GetHash();

        if(!CheckProofOfStake(block, hashProofOfStake)) {
            LogPrintf("WARNING: ProcessBlock(): check proof-of-stake failed for block %s\n", hash.ToString().c_str());
            return false;
        }
        if(!mapProofOfStake.count(hash)) // add to mapProofOfStake
            mapProofOfStake.insert(make_pair(hash, hashProofOfStake));
    }

    return true;
}

bool ContextualCheckBlockHeader(const CBlockHeader& block, CValidationState& state, CBlockIndex* const pindexPrev)
{
    uint256 hash = block.GetHash();

    if (hash == Params().HashGenesisBlock())
        return true;

    assert(pindexPrev);

    int nHeight = pindexPrev->nHeight + 1;

    //If this is a reorg, check that it is not too depp
    if (chainActive.Height() - nHeight >= Params().MaxReorganizationDepth())
        return state.DoS(1, error("%s: forked chain older than max reorganization depth (height %d)", __func__, nHeight));

    // Check timestamp against prev
    if (block.GetBlockTime() <= pindexPrev->GetMedianTimePast()) {
        LogPrintf("Block time = %d , GetMedianTimePast = %d \n", block.GetBlockTime(), pindexPrev->GetMedianTimePast());
        return state.Invalid(error("%s : block's timestamp is too early", __func__),
            REJECT_INVALID, "time-too-old");
    }

    // Check that the block chain matches the known block chain up to a checkpoint
    if (!Checkpoints::CheckBlock(nHeight, hash))
        return state.DoS(100, error("%s : rejected by checkpoint lock-in at %d", __func__, nHeight),
            REJECT_CHECKPOINT, "checkpoint mismatch");

    // Don't accept any forks from the main chain prior to last checkpoint
    CBlockIndex* pcheckpoint = Checkpoints::GetLastCheckpoint();
    if (pcheckpoint && nHeight < pcheckpoint->nHeight)
        return state.DoS(0, error("%s : forked chain older than last checkpoint (height %d)", __func__, nHeight));

    // Reject block.nVersion=1 blocks when 95% (75% on testnet) of the network has upgraded:
    if (block.nVersion < 2 &&
        CBlockIndex::IsSuperMajority(2, pindexPrev, Params().RejectBlockOutdatedMajority())) {
        return state.Invalid(error("%s : rejected nVersion=1 block", __func__),
            REJECT_OBSOLETE, "bad-version");
    }

    // Reject block.nVersion=2 blocks when 95% (75% on testnet) of the network has upgraded:
    if (block.nVersion < 3 && CBlockIndex::IsSuperMajority(3, pindexPrev, Params().RejectBlockOutdatedMajority())) {
        return state.Invalid(error("%s : rejected nVersion=2 block", __func__),
            REJECT_OBSOLETE, "bad-version");
    }

    return true;
}

bool ContextualCheckBlock(const CBlock& block, CValidationState& state, CBlockIndex* const pindexPrev)
{
    const int nHeight = pindexPrev == NULL ? 0 : pindexPrev->nHeight + 1;

    // Check that all transactions are finalized
    BOOST_FOREACH (const CTransaction& tx, block.vtx)
        if (!IsFinalTx(tx, nHeight, block.GetBlockTime())) {
            return state.DoS(10, error("%s : contains a non-final transaction", __func__), REJECT_INVALID, "bad-txns-nonfinal");
        }

    // Enforce block.nVersion=2 rule that the coinbase starts with serialized block height
    // if 750 of the last 1,000 blocks are version 2 or greater (51/100 if testnet):
    if (block.nVersion >= 2 &&
        CBlockIndex::IsSuperMajority(2, pindexPrev, Params().EnforceBlockUpgradeMajority())) {
        CScript expect = CScript() << nHeight;
        if (block.vtx[0].vin[0].scriptSig.size() < expect.size() ||
            !std::equal(expect.begin(), expect.end(), block.vtx[0].vin[0].scriptSig.begin())) {
            return state.DoS(100, error("%s : block height mismatch in coinbase", __func__), REJECT_INVALID, "bad-cb-height");
        }
    }

    return true;
}

bool AcceptBlockHeader(const CBlock& block, CValidationState& state, CBlockIndex** ppindex)
{
    AssertLockHeld(cs_main);
    // Check for duplicate
    uint256 hash = block.GetHash();
    BlockMap::iterator miSelf = mapBlockIndex.find(hash);
    CBlockIndex* pindex = NULL;

    // TODO : ENABLE BLOCK CACHE IN SPECIFIC CASES
    if (miSelf != mapBlockIndex.end()) {
        // Block header is already known.
        pindex = miSelf->second;
        if (ppindex)
            *ppindex = pindex;
        if (pindex->nStatus & BLOCK_FAILED_MASK)
            return state.Invalid(error("%s : block is marked invalid", __func__), 0, "duplicate");
        return true;
    }

    if (!CheckBlockHeader(block, state, false)) {
        LogPrintf("AcceptBlockHeader(): CheckBlockHeader failed \n");
        return false;
    }

    // Get prev block index
    CBlockIndex* pindexPrev = NULL;
    if (hash != Params().HashGenesisBlock()) {
        BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
        if (mi == mapBlockIndex.end())
            return state.DoS(0, error("%s : prev block %s not found", __func__, block.hashPrevBlock.ToString().c_str()), 0, "bad-prevblk");
        pindexPrev = (*mi).second;
        if (pindexPrev->nStatus & BLOCK_FAILED_MASK)
            return state.DoS(100, error("%s : prev block invalid", __func__), REJECT_INVALID, "bad-prevblk");
    }

    if (!ContextualCheckBlockHeader(block, state, pindexPrev))
        return false;

    if (pindex == NULL)
        pindex = AddToBlockIndex(block);

    if (ppindex)
        *ppindex = pindex;

    return true;
}

bool AcceptBlock(CBlock& block, CValidationState& state, CBlockIndex** ppindex, CDiskBlockPos* dbp)
{
    AssertLockHeld(cs_main);

    CBlockIndex*& pindex = *ppindex;

    // Get prev block index
    CBlockIndex* pindexPrev = NULL;
    if (block.GetHash() != Params().HashGenesisBlock()) {
        BlockMap::iterator mi = mapBlockIndex.find(block.hashPrevBlock);
        if (mi == mapBlockIndex.end())
            return state.DoS(0, error("%s : prev block %s not found", __func__, block.hashPrevBlock.ToString().c_str()), 0, "bad-prevblk");
        pindexPrev = (*mi).second;
        if (pindexPrev->nStatus & BLOCK_FAILED_MASK)
            return state.DoS(100, error("%s : prev block invalid", __func__), REJECT_INVALID, "bad-prevblk");
    }

    if (block.GetHash() != Params().HashGenesisBlock() && !CheckWork(block, pindexPrev))
        return false;

    if (!AcceptBlockHeader(block, state, &pindex))
        return false;

    if (pindex->nStatus & BLOCK_HAVE_DATA) {
        // TODO: deal better with duplicate blocks.
        // return state.DoS(20, error("AcceptBlock() : already have block %d %s", pindex->nHeight, pindex->GetBlockHash().ToString()), REJECT_DUPLICATE, "duplicate");
        return true;
    }

    if ((!CheckBlock(block, state)) || !ContextualCheckBlock(block, state, pindex->pprev)) {
        if (state.IsInvalid() && !state.CorruptionPossible()) {
            pindex->nStatus |= BLOCK_FAILED_VALID;
            setDirtyBlockIndex.insert(pindex);
        }
        return false;
    }

    int nHeight = pindex->nHeight;

	if (block.IsProofOfStake()) {
		LOCK(cs_main);

		CCoinsViewCache coins(pcoinsTip);

		if (!coins.HaveInputs(block.vtx[1])) {
			// the inputs are spent at the chain tip so we should look at the recently spent outputs

			for (CTxIn in : block.vtx[1].vin) {
				auto it = mapStakeSpent.find(in.prevout);
				if (it == mapStakeSpent.end()) {
					return false;
				}
				if (it->second <= pindexPrev->nHeight) {
					return false;
				}
			}
		}

		// if this is on a fork
		if (!chainActive.Contains(pindexPrev)) {
			// start at the block we're adding on to
			CBlockIndex *last = pindexPrev;

			// while that block is not on the main chain
			while (!chainActive.Contains(last)) {
				CBlock bl;
				ReadBlockFromDisk(bl, last);
				// loop through every spent input from said block
				for (CTransaction t : bl.vtx) {
					for (CTxIn in : t.vin) {
						// loop through every spent input in the staking transaction of the new block
						for (CTxIn stakeIn : block.vtx[1].vin) {
							// if they spend the same input
							if (stakeIn.prevout == in.prevout) {
								// reject the block
								return false;
							}
						}
					}
				}

				// go to the parent block
				last = pindexPrev->pprev;
			}
		}
	}

    // Write block to history file
    try {
        unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
        CDiskBlockPos blockPos;
        if (dbp != NULL)
            blockPos = *dbp;
        if (!FindBlockPos(state, blockPos, nBlockSize + 8, nHeight, block.GetBlockTime(), dbp != NULL))
            return error("AcceptBlock() : FindBlockPos failed");
        if (dbp == NULL)
            if (!WriteBlockToDisk(block, blockPos))
                return state.Abort("Failed to write block");
        if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
            return error("AcceptBlock() : ReceivedBlockTransactions failed");
    } catch (std::runtime_error& e) {
        return state.Abort(std::string("System error: ") + e.what());
    }

    return true;
}

bool CBlockIndex::IsSuperMajority(int minVersion, const CBlockIndex* pstart, unsigned int nRequired)
{
    unsigned int nToCheck = Params().ToCheckBlockUpgradeMajority();
    unsigned int nFound = 0;
    for (unsigned int i = 0; i < nToCheck && nFound < nRequired && pstart != NULL; i++) {
        if (pstart->nVersion >= minVersion)
            ++nFound;
        pstart = pstart->pprev;
    }
    return (nFound >= nRequired);
}

/** Turn the lowest '1' bit in the binary representation of a number into a '0'. */
int static inline InvertLowestOne(int n) { return n & (n - 1); }

/** Compute what height to jump back to with the CBlockIndex::pskip pointer. */
int static inline GetSkipHeight(int height)
{
    if (height < 2)
        return 0;

    // Determine which height to jump back to. Any number strictly lower than height is acceptable,
    // but the following expression seems to perform well in simulations (max 110 steps to go back
    // up to 2**18 blocks).
    return (height & 1) ? InvertLowestOne(InvertLowestOne(height - 1)) + 1 : InvertLowestOne(height);
}

CBlockIndex* CBlockIndex::GetAncestor(int height)
{
    if (height > nHeight || height < 0)
        return NULL;

    CBlockIndex* pindexWalk = this;
    int heightWalk = nHeight;
    while (heightWalk > height) {
        int heightSkip = GetSkipHeight(heightWalk);
        int heightSkipPrev = GetSkipHeight(heightWalk - 1);
        if (heightSkip == height ||
            (heightSkip > height && !(heightSkipPrev < heightSkip - 2 && heightSkipPrev >= height))) {
            // Only follow pskip if pprev->pskip isn't better than pskip->pprev.
            pindexWalk = pindexWalk->pskip;
            heightWalk = heightSkip;
        } else {
            pindexWalk = pindexWalk->pprev;
            heightWalk--;
        }
    }
    return pindexWalk;
}

const CBlockIndex* CBlockIndex::GetAncestor(int height) const
{
    return const_cast<CBlockIndex*>(this)->GetAncestor(height);
}

void CBlockIndex::BuildSkip()
{
    if (pprev)
        pskip = pprev->GetAncestor(GetSkipHeight(nHeight));
}

bool ProcessNewBlock(CValidationState& state, CNode* pfrom, CBlock* pblock, CDiskBlockPos* dbp)
{
    // Preliminary checks
    bool checked = CheckBlock(*pblock, state);

    // ppcoin: check proof-of-stake
    // Limited duplicity on stake: prevents block flood attack
    // Duplicate stake allowed only when there is orphan child block
    //if (pblock->IsProofOfStake() && setStakeSeen.count(pblock->GetProofOfStake())/* && !mapOrphanBlocksByPrev.count(hash)*/)
    //    return error("ProcessNewBlock() : duplicate proof-of-stake (%s, %d) for block %s", pblock->GetProofOfStake().first.ToString().c_str(), pblock->GetProofOfStake().second, pblock->GetHash().ToString().c_str());

    // NovaCoin: check proof-of-stake block signature
    if (!pblock->CheckBlockSignature())
        return error("ProcessNewBlock() : bad proof-of-stake block signature");

    if (pblock->GetHash() != Params().HashGenesisBlock() && pfrom != NULL) {
        //if we get this far, check if the prev block is our prev block, if not then request sync and return false
        BlockMap::iterator mi = mapBlockIndex.find(pblock->hashPrevBlock);
        if (mi == mapBlockIndex.end()) {
            pfrom->PushMessage("getblocks", chainActive.GetLocator(), uint256(0));
            return false;
        }
    }

    while (true) {
        TRY_LOCK(cs_main, lockMain);
        if (!lockMain) {
            MilliSleep(50);
            continue;
        }

        MarkBlockAsReceived(pblock->GetHash());
        if (!checked) {
            return error("%s : CheckBlock FAILED", __func__);
        }

        // Store to disk
        CBlockIndex* pindex = NULL;
        bool ret = AcceptBlock(*pblock, state, &pindex, dbp);
        if (pindex && pfrom) {
            mapBlockSource[pindex->GetBlockHash()] = pfrom->GetId();
        }
        CheckBlockIndex();
        if (!ret)
            return error("%s : AcceptBlock FAILED", __func__);
        break;
    }

    if (!ActivateBestChain(state, pblock))
        return error("%s : ActivateBestChain failed", __func__);

    if (!fLiteMode) {
        if (masternodeSync.RequestedMasternodeAssets > MASTERNODE_SYNC_LIST) {
            obfuScationPool.NewBlock();
            masternodePayments.ProcessBlock(GetHeight() + 10);
            budget.NewBlock();
        }
    }

    if (pwalletMain) {
        // If turned on MultiSend will send a transaction (or more) on the after maturity of a stake
        if (pwalletMain->isMultiSendEnabled())
            pwalletMain->MultiSend();

        //If turned on Auto Combine will scan wallet for dust to combine
        if (pwalletMain->fCombineDust)
            pwalletMain->AutoCombineDust();
    }

    LogPrintf("%s : ACCEPTED\n", __func__);

    return true;
}

bool TestBlockValidity(CValidationState& state, const CBlock& block, CBlockIndex* const pindexPrev, bool fCheckPOW, bool fCheckMerkleRoot)
{
    AssertLockHeld(cs_main);
    assert(pindexPrev == chainActive.Tip());

    CCoinsViewCache viewNew(pcoinsTip);
    CBlockIndex indexDummy(block);
    indexDummy.pprev = pindexPrev;
    indexDummy.nHeight = pindexPrev->nHeight + 1;

    // NOTE: CheckBlockHeader is called by CheckBlock
    if (!ContextualCheckBlockHeader(block, state, pindexPrev))
        return false;
    if (!CheckBlock(block, state, fCheckPOW, fCheckMerkleRoot))
        return false;
    if (!ContextualCheckBlock(block, state, pindexPrev))
        return false;
    if (!ConnectBlock(block, state, &indexDummy, viewNew, true))
        return false;
    assert(state.IsValid());

    return true;
}


bool AbortNode(const std::string& strMessage, const std::string& userMessage)
{
    strMiscWarning = strMessage;
    LogPrintf("*** %s\n", strMessage);
    uiInterface.ThreadSafeMessageBox(
        userMessage.empty() ? _("Error: A fatal internal error occured, see debug.log for details") : userMessage,
        "", CClientUIInterface::MSG_ERROR);
    StartShutdown();
    return false;
}

bool CheckDiskSpace(uint64_t nAdditionalBytes)
{
    uint64_t nFreeBytesAvailable = filesystem::space(GetDataDir()).available;

    // Check for nMinDiskSpace bytes (currently 50MB)
    if (nFreeBytesAvailable < nMinDiskSpace + nAdditionalBytes)
        return AbortNode("Disk space is low!", _("Error: Disk space is low!"));

    return true;
}

FILE* OpenDiskFile(const CDiskBlockPos& pos, const char* prefix, bool fReadOnly)
{
    if (pos.IsNull())
        return NULL;
    boost::filesystem::path path = GetBlockPosFilename(pos, prefix);
    boost::filesystem::create_directories(path.parent_path());
    FILE* file = fopen(path.string().c_str(), "rb+");
    if (!file && !fReadOnly)
        file = fopen(path.string().c_str(), "wb+");
    if (!file) {
        LogPrintf("Unable to open file %s\n", path.string());
        return NULL;
    }
    if (pos.nPos) {
        if (fseek(file, pos.nPos, SEEK_SET)) {
            LogPrintf("Unable to seek to position %u of %s\n", pos.nPos, path.string());
            fclose(file);
            return NULL;
        }
    }
    return file;
}

FILE* OpenBlockFile(const CDiskBlockPos& pos, bool fReadOnly)
{
    return OpenDiskFile(pos, "blk", fReadOnly);
}

FILE* OpenUndoFile(const CDiskBlockPos& pos, bool fReadOnly)
{
    return OpenDiskFile(pos, "rev", fReadOnly);
}

boost::filesystem::path GetBlockPosFilename(const CDiskBlockPos& pos, const char* prefix)
{
    return GetDataDir() / "blocks" / strprintf("%s%05u.dat", prefix, pos.nFile);
}

CBlockIndex* InsertBlockIndex(uint256 hash)
{
    if (hash == 0)
        return NULL;

    // Return existing
    BlockMap::iterator mi = mapBlockIndex.find(hash);
    if (mi != mapBlockIndex.end())
        return (*mi).second;

    // Create new
    CBlockIndex* pindexNew = new CBlockIndex();
    if (!pindexNew)
        throw runtime_error("LoadBlockIndex() : new CBlockIndex failed");
    mi = mapBlockIndex.insert(make_pair(hash, pindexNew)).first;

    //mark as PoS seen
    if (pindexNew->IsProofOfStake())
        setStakeSeen.insert(make_pair(pindexNew->prevoutStake, pindexNew->nStakeTime));

    pindexNew->phashBlock = &((*mi).first);

    return pindexNew;
}

bool static LoadBlockIndexDB()
{
    if (!pblocktree->LoadBlockIndexGuts())
        return false;

    boost::this_thread::interruption_point();

    // Calculate nChainWork
    vector<pair<int, CBlockIndex*> > vSortedByHeight;
    vSortedByHeight.reserve(mapBlockIndex.size());
    BOOST_FOREACH (const PAIRTYPE(uint256, CBlockIndex*) & item, mapBlockIndex) {
        CBlockIndex* pindex = item.second;
        vSortedByHeight.push_back(make_pair(pindex->nHeight, pindex));
    }
    sort(vSortedByHeight.begin(), vSortedByHeight.end());
    BOOST_FOREACH (const PAIRTYPE(int, CBlockIndex*) & item, vSortedByHeight) {
        CBlockIndex* pindex = item.second;
        pindex->nChainWork = (pindex->pprev ? pindex->pprev->nChainWork : 0) + GetBlockProof(*pindex);
        if (pindex->nStatus & BLOCK_HAVE_DATA) {
            if (pindex->pprev) {
                if (pindex->pprev->nChainTx) {
                    pindex->nChainTx = pindex->pprev->nChainTx + pindex->nTx;
                } else {
                    pindex->nChainTx = 0;
                    mapBlocksUnlinked.insert(std::make_pair(pindex->pprev, pindex));
                }
            } else {
                pindex->nChainTx = pindex->nTx;
            }
        }
        if (pindex->IsValid(BLOCK_VALID_TRANSACTIONS) && (pindex->nChainTx || pindex->pprev == NULL))
            setBlockIndexCandidates.insert(pindex);
        if (pindex->nStatus & BLOCK_FAILED_MASK && (!pindexBestInvalid || pindex->nChainWork > pindexBestInvalid->nChainWork))
            pindexBestInvalid = pindex;
        if (pindex->pprev)
            pindex->BuildSkip();
        if (pindex->IsValid(BLOCK_VALID_TREE) && (pindexBestHeader == NULL || CBlockIndexWorkComparator()(pindexBestHeader, pindex)))
            pindexBestHeader = pindex;
    }

    // Load block file info
    pblocktree->ReadLastBlockFile(nLastBlockFile);
    vinfoBlockFile.resize(nLastBlockFile + 1);
    LogPrintf("%s: last block file = %i\n", __func__, nLastBlockFile);
    for (int nFile = 0; nFile <= nLastBlockFile; nFile++) {
        pblocktree->ReadBlockFileInfo(nFile, vinfoBlockFile[nFile]);
    }
    LogPrintf("%s: last block file info: %s\n", __func__, vinfoBlockFile[nLastBlockFile].ToString());
    for (int nFile = nLastBlockFile + 1; true; nFile++) {
        CBlockFileInfo info;
        if (pblocktree->ReadBlockFileInfo(nFile, info)) {
            vinfoBlockFile.push_back(info);
        } else {
            break;
        }
    }

    // Check presence of blk files
    LogPrintf("Checking all blk files are present...\n");
    set<int> setBlkDataFiles;
    BOOST_FOREACH (const PAIRTYPE(uint256, CBlockIndex*) & item, mapBlockIndex) {
        CBlockIndex* pindex = item.second;
        if (pindex->nStatus & BLOCK_HAVE_DATA) {
            setBlkDataFiles.insert(pindex->nFile);
        }
    }
    for (std::set<int>::iterator it = setBlkDataFiles.begin(); it != setBlkDataFiles.end(); it++) {
        CDiskBlockPos pos(*it, 0);
        if (CAutoFile(OpenBlockFile(pos, true), SER_DISK, CLIENT_VERSION).IsNull()) {
            return false;
        }
    }

    //Check if the shutdown procedure was followed on last client exit
    bool fLastShutdownWasPrepared = true;
    pblocktree->ReadFlag("shutdown", fLastShutdownWasPrepared);
    LogPrintf("%s: Last shutdown was prepared: %s\n", __func__, fLastShutdownWasPrepared);

    //Check for inconsistency with block file info and internal state
    if (!fLastShutdownWasPrepared && !GetBoolArg("-forcestart", false) && !GetBoolArg("-reindex", false) && (vSortedByHeight.size() != vinfoBlockFile[nLastBlockFile].nHeightLast + 1) && (vinfoBlockFile[nLastBlockFile].nHeightLast != 0)) {
        //The database is in a state where a block has been accepted and written to disk, but not
        //all of the block has perculated through the code. The block and the index should both be
        //intact (although assertions are added if they are not), and the block will be reprocessed
        //to ensure all data will be accounted for.
        LogPrintf("%s: Inconsistent State Detected mapBlockIndex.size()=%d blockFileBlocks=%d\n", __func__, vSortedByHeight.size(), vinfoBlockFile[nLastBlockFile].nHeightLast + 1);
        LogPrintf("%s: lastIndexPos=%d blockFileSize=%d\n", __func__, vSortedByHeight[vSortedByHeight.size() - 1].second->GetBlockPos().nPos,
            vinfoBlockFile[nLastBlockFile].nSize);

        //try reading the block from the last index we have
        bool isFixed = true;
        string strError = "";
        LogPrintf("%s: Attempting to re-add last block that was recorded to disk\n", __func__);

        //get the last block that was properly recorded to the block info file
        CBlockIndex* pindexLastMeta = vSortedByHeight[vinfoBlockFile[nLastBlockFile].nHeightLast + 1].second;

        //fix Assertion `hashPrevBlock == view.GetBestBlock()' failed. By adjusting height to the last recorded by coinsview
        CBlockIndex* pindexCoinsView = mapBlockIndex[pcoinsTip->GetBestBlock()];
        for(unsigned int i = vinfoBlockFile[nLastBlockFile].nHeightLast + 1; i < vSortedByHeight.size(); i++)
        {
            pindexLastMeta = vSortedByHeight[i].second;
            if(pindexLastMeta->nHeight > pindexCoinsView->nHeight)
                break;
        }

        LogPrintf("%s: Last block properly recorded: #%d %s\n", __func__, pindexLastMeta->nHeight, pindexLastMeta->GetBlockHash().ToString().c_str());

        CBlock lastMetaBlock;
        if (!ReadBlockFromDisk(lastMetaBlock, pindexLastMeta)) {
            isFixed = false;
            strError = strprintf("failed to read block %d from disk", pindexLastMeta->nHeight);
        }

        //set the chain to the block before lastMeta so that the meta block will be seen as new
        chainActive.SetTip(pindexLastMeta->pprev);

        //Process the lastMetaBlock again, using the known location on disk
        CDiskBlockPos blockPos = pindexLastMeta->GetBlockPos();
        CValidationState state;
        ProcessNewBlock(state, NULL, &lastMetaBlock, &blockPos);

        //ensure that everything is as it should be
        if (pcoinsTip->GetBestBlock() != vSortedByHeight[vSortedByHeight.size() - 1].second->GetBlockHash()) {
            isFixed = false;
            strError = "pcoinsTip best block is not correct";
        }

        //properly account for all of the blocks that were not in the meta data. If this is not done the file
        //positioning will be wrong and blocks will be overwritten and later cause serialization errors
        CBlockIndex *pindexLast = vSortedByHeight[vSortedByHeight.size() - 1].second;
        CBlock lastBlock;
        if (!ReadBlockFromDisk(lastBlock, pindexLast)) {
            isFixed = false;
            strError = strprintf("failed to read block %d from disk", pindexLast->nHeight);
        }
        vinfoBlockFile[nLastBlockFile].nHeightLast = pindexLast->nHeight;
        vinfoBlockFile[nLastBlockFile].nSize = pindexLast->GetBlockPos().nPos + ::GetSerializeSize(lastBlock, SER_DISK, CLIENT_VERSION);;
        setDirtyFileInfo.insert(nLastBlockFile);
        FlushStateToDisk(state, FLUSH_STATE_ALWAYS);

        //Print out file info again
        pblocktree->ReadLastBlockFile(nLastBlockFile);
        vinfoBlockFile.resize(nLastBlockFile + 1);
        LogPrintf("%s: last block file = %i\n", __func__, nLastBlockFile);
        for (int nFile = 0; nFile <= nLastBlockFile; nFile++) {
            pblocktree->ReadBlockFileInfo(nFile, vinfoBlockFile[nFile]);
        }
        LogPrintf("%s: last block file info: %s\n", __func__, vinfoBlockFile[nLastBlockFile].ToString());

        if (!isFixed) {
            strError = "Failed reading from database. " + strError + ". The block database is in an inconsistent state and may cause issues in the future."
                                                                     "To force start use -forcestart";
            uiInterface.ThreadSafeMessageBox(strError, "", CClientUIInterface::MSG_ERROR);
            abort();
        }
        LogPrintf("Passed corruption fix\n");
    }

    // Check whether we need to continue reindexing
    bool fReindexing = false;
    pblocktree->ReadReindexing(fReindexing);
    fReindex |= fReindexing;

    // Check whether we have a transaction index
    pblocktree->ReadFlag("txindex", fTxIndex);
    LogPrintf("LoadBlockIndexDB(): transaction index %s\n", fTxIndex ? "enabled" : "disabled");

    // If this is written true before the next client init, then we know the shutdown process failed
    pblocktree->WriteFlag("shutdown", false);

    // Load pointer to end of best chain
    BlockMap::iterator it = mapBlockIndex.find(pcoinsTip->GetBestBlock());
    if (it == mapBlockIndex.end())
        return true;
    chainActive.SetTip(it->second);

    PruneBlockIndexCandidates();

    LogPrintf("LoadBlockIndexDB(): hashBestChain=%s height=%d date=%s progress=%f\n",
        chainActive.Tip()->GetBlockHash().ToString(), chainActive.Height(),
        DateTimeStrFormat("%Y-%m-%d %H:%M:%S", chainActive.Tip()->GetBlockTime()),
        Checkpoints::GuessVerificationProgress(chainActive.Tip()));

    return true;
}

CVerifyDB::CVerifyDB()
{
    uiInterface.ShowProgress(_("Verifying blocks..."), 0);
}

CVerifyDB::~CVerifyDB()
{
    uiInterface.ShowProgress("", 100);
}

bool CVerifyDB::VerifyDB(CCoinsView* coinsview, int nCheckLevel, int nCheckDepth)
{
    LOCK(cs_main);
    if (chainActive.Tip() == NULL || chainActive.Tip()->pprev == NULL)
        return true;

    // Verify blocks in the best chain
    if (nCheckDepth <= 0)
        nCheckDepth = 1000000000; // suffices until the year 19000
    if (nCheckDepth > chainActive.Height())
        nCheckDepth = chainActive.Height();
    nCheckLevel = std::max(0, std::min(4, nCheckLevel));
    LogPrintf("Verifying last %i blocks at level %i\n", nCheckDepth, nCheckLevel);
    CCoinsViewCache coins(coinsview);
    CBlockIndex* pindexState = chainActive.Tip();
    CBlockIndex* pindexFailure = NULL;
    int nGoodTransactions = 0;
    CValidationState state;
    for (CBlockIndex* pindex = chainActive.Tip(); pindex && pindex->pprev; pindex = pindex->pprev) {
        boost::this_thread::interruption_point();
        uiInterface.ShowProgress(_("Verifying blocks..."), std::max(1, std::min(99, (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * (nCheckLevel >= 4 ? 50 : 100)))));
        if (pindex->nHeight < chainActive.Height() - nCheckDepth)
            break;
        CBlock block;
        // check level 0: read from disk
        if (!ReadBlockFromDisk(block, pindex))
            return error("VerifyDB() : *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
        // check level 1: verify block validity
        if (nCheckLevel >= 1 && !CheckBlock(block, state))
            return error("VerifyDB() : *** found bad block at %d, hash=%s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
        // check level 2: verify undo validity
        if (nCheckLevel >= 2 && pindex) {
            CBlockUndo undo;
            CDiskBlockPos pos = pindex->GetUndoPos();
            if (!pos.IsNull()) {
                if (!undo.ReadFromDisk(pos, pindex->pprev->GetBlockHash()))
                    return error("VerifyDB() : *** found bad undo data at %d, hash=%s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
            }
        }
        // check level 3: check for inconsistencies during memory-only disconnect of tip blocks
        if (nCheckLevel >= 3 && pindex == pindexState && (coins.GetCacheSize() + pcoinsTip->GetCacheSize()) <= nCoinCacheSize) {
            bool fClean = true;
            if (!DisconnectBlock(block, state, pindex, coins, &fClean))
                return error("VerifyDB() : *** irrecoverable inconsistency in block data at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
            pindexState = pindex->pprev;
            if (!fClean) {
                nGoodTransactions = 0;
                pindexFailure = pindex;
            } else
                nGoodTransactions += block.vtx.size();
        }
        if (ShutdownRequested())
            return true;
    }
    if (pindexFailure)
        return error("VerifyDB() : *** coin database inconsistencies found (last %i blocks, %i good transactions before that)\n", chainActive.Height() - pindexFailure->nHeight + 1, nGoodTransactions);

    // check level 4: try reconnecting blocks
    if (nCheckLevel >= 4) {
        CBlockIndex* pindex = pindexState;
        while (pindex != chainActive.Tip()) {
            boost::this_thread::interruption_point();
            uiInterface.ShowProgress(_("Verifying blocks..."), std::max(1, std::min(99, 100 - (int)(((double)(chainActive.Height() - pindex->nHeight)) / (double)nCheckDepth * 50))));
            pindex = chainActive.Next(pindex);
            CBlock block;
            if (!ReadBlockFromDisk(block, pindex))
                return error("VerifyDB() : *** ReadBlockFromDisk failed at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
            if (!ConnectBlock(block, state, pindex, coins))
                return error("VerifyDB() : *** found unconnectable block at %d, hash=%s", pindex->nHeight, pindex->GetBlockHash().ToString());
        }
    }

    LogPrintf("No coin database inconsistencies in last %i blocks (%i transactions)\n", chainActive.Height() - pindexState->nHeight, nGoodTransactions);

    return true;
}

void UnloadBlockIndex()
{
    mapBlockIndex.clear();
    setBlockIndexCandidates.clear();
    chainActive.SetTip(NULL);
    pindexBestInvalid = NULL;
}

bool LoadBlockIndex()
{
    // Load block index from databases
    if (!fReindex && !LoadBlockIndexDB())
        return false;
    return true;
}


bool InitBlockIndex()
{
    LOCK(cs_main);
    // Check whether we're already initialized
    if (chainActive.Genesis() != NULL)
        return true;

    // Use the provided setting for -txindex in the new database
    fTxIndex = GetBoolArg("-txindex", true);
    pblocktree->WriteFlag("txindex", fTxIndex);
    LogPrintf("Initializing databases...\n");

    // Only add the genesis block if not reindexing (in which case we reuse the one already on disk)
    if (!fReindex) {
        try {
            CBlock& block = const_cast<CBlock&>(Params().GenesisBlock());
            // Start new block file
            unsigned int nBlockSize = ::GetSerializeSize(block, SER_DISK, CLIENT_VERSION);
            CDiskBlockPos blockPos;
            CValidationState state;
            if (!FindBlockPos(state, blockPos, nBlockSize + 8, 0, block.GetBlockTime()))
                return error("LoadBlockIndex() : FindBlockPos failed");
            if (!WriteBlockToDisk(block, blockPos))
                return error("LoadBlockIndex() : writing genesis block to disk failed");
            CBlockIndex* pindex = AddToBlockIndex(block);
            if (!ReceivedBlockTransactions(block, state, pindex, blockPos))
                return error("LoadBlockIndex() : genesis block not accepted");
            if (!ActivateBestChain(state, &block))
                return error("LoadBlockIndex() : genesis block cannot be activated");
            // Force a chainstate write so that when we VerifyDB in a moment, it doesnt check stale data
            return FlushStateToDisk(state, FLUSH_STATE_ALWAYS);
        } catch (std::runtime_error& e) {
            return error("LoadBlockIndex() : failed to initialize block database: %s", e.what());
        }
    }

    return true;
}


bool LoadExternalBlockFile(FILE* fileIn, CDiskBlockPos* dbp)
{
    // Map of disk positions for blocks with unknown parent (only used for reindex)
    static std::multimap<uint256, CDiskBlockPos> mapBlocksUnknownParent;
    int64_t nStart = GetTimeMillis();

    int nLoaded = 0;
    try {
        // This takes over fileIn and calls fclose() on it in the CBufferedFile destructor
        CBufferedFile blkdat(fileIn, 2 * MAX_BLOCK_SIZE, MAX_BLOCK_SIZE + 8, SER_DISK, CLIENT_VERSION);
        uint64_t nRewind = blkdat.GetPos();
        while (!blkdat.eof()) {
            boost::this_thread::interruption_point();

            blkdat.SetPos(nRewind);
            nRewind++;         // start one byte further next time, in case of failure
            blkdat.SetLimit(); // remove former limit
            unsigned int nSize = 0;
            try {
                // locate a header
                unsigned char buf[MESSAGE_START_SIZE];
                blkdat.FindByte(Params().MessageStart()[0]);
                nRewind = blkdat.GetPos() + 1;
                blkdat >> FLATDATA(buf);
                if (memcmp(buf, Params().MessageStart(), MESSAGE_START_SIZE))
                    continue;
                // read size
                blkdat >> nSize;
                if (nSize < 80 || nSize > MAX_BLOCK_SIZE)
                    continue;
            } catch (const std::exception&) {
                // no valid block header found; don't complain
                break;
            }
            try {
                // read block
                uint64_t nBlockPos = blkdat.GetPos();
                if (dbp)
                    dbp->nPos = nBlockPos;
                blkdat.SetLimit(nBlockPos + nSize);
                blkdat.SetPos(nBlockPos);
                CBlock block;
                blkdat >> block;
                nRewind = blkdat.GetPos();

                // detect out of order blocks, and store them for later
                uint256 hash = block.GetHash();
                if (hash != Params().HashGenesisBlock() && mapBlockIndex.find(block.hashPrevBlock) == mapBlockIndex.end()) {
                    LogPrint("reindex", "%s: Out of order block %s, parent %s not known\n", __func__, hash.ToString(),
                        block.hashPrevBlock.ToString());
                    if (dbp)
                        mapBlocksUnknownParent.insert(std::make_pair(block.hashPrevBlock, *dbp));
                    continue;
                }

                // process in case the block isn't known yet
                if (mapBlockIndex.count(hash) == 0 || (mapBlockIndex[hash]->nStatus & BLOCK_HAVE_DATA) == 0) {
                    CValidationState state;
                    if (ProcessNewBlock(state, NULL, &block, dbp))
                        nLoaded++;
                    if (state.IsError())
                        break;
                } else if (hash != Params().HashGenesisBlock() && mapBlockIndex[hash]->nHeight % 1000 == 0) {
                    LogPrintf("Block Import: already had block %s at height %d\n", hash.ToString(), mapBlockIndex[hash]->nHeight);
                }

                // Recursively process earlier encountered successors of this block
                deque<uint256> queue;
                queue.push_back(hash);
                while (!queue.empty()) {
                    uint256 head = queue.front();
                    queue.pop_front();
                    std::pair<std::multimap<uint256, CDiskBlockPos>::iterator, std::multimap<uint256, CDiskBlockPos>::iterator> range = mapBlocksUnknownParent.equal_range(head);
                    while (range.first != range.second) {
                        std::multimap<uint256, CDiskBlockPos>::iterator it = range.first;
                        if (ReadBlockFromDisk(block, it->second)) {
                            LogPrintf("%s: Processing out of order child %s of %s\n", __func__, block.GetHash().ToString(),
                                head.ToString());
                            CValidationState dummy;
                            if (ProcessNewBlock(dummy, NULL, &block, &it->second)) {
                                nLoaded++;
                                queue.push_back(block.GetHash());
                            }
                        }
                        range.first++;
                        mapBlocksUnknownParent.erase(it);
                    }
                }
            } catch (std::exception& e) {
                LogPrintf("%s : Deserialize or I/O error - %s", __func__, e.what());
            }
        }
    } catch (std::runtime_error& e) {
        AbortNode(std::string("System error: ") + e.what());
    }
    if (nLoaded > 0)
        LogPrintf("Loaded %i blocks from external file in %dms\n", nLoaded, GetTimeMillis() - nStart);
    return nLoaded > 0;
}

void static CheckBlockIndex()
{
    if (!fCheckBlockIndex) {
        return;
    }

    LOCK(cs_main);

    // During a reindex, we read the genesis block and call CheckBlockIndex before ActivateBestChain,
    // so we have the genesis block in mapBlockIndex but no active chain.  (A few of the tests when
    // iterating the block tree require that chainActive has been initialized.)
    if (chainActive.Height() < 0) {
        assert(mapBlockIndex.size() <= 1);
        return;
    }

    // Build forward-pointing map of the entire block tree.
    std::multimap<CBlockIndex*, CBlockIndex*> forward;
    for (BlockMap::iterator it = mapBlockIndex.begin(); it != mapBlockIndex.end(); it++) {
        forward.insert(std::make_pair(it->second->pprev, it->second));
    }

    assert(forward.size() == mapBlockIndex.size());

    std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangeGenesis = forward.equal_range(NULL);
    CBlockIndex* pindex = rangeGenesis.first->second;
    rangeGenesis.first++;
    assert(rangeGenesis.first == rangeGenesis.second); // There is only one index entry with parent NULL.

    // Iterate over the entire block tree, using depth-first search.
    // Along the way, remember whether there are blocks on the path from genesis
    // block being explored which are the first to have certain properties.
    size_t nNodes = 0;
    int nHeight = 0;
    CBlockIndex* pindexFirstInvalid = NULL;         // Oldest ancestor of pindex which is invalid.
    CBlockIndex* pindexFirstMissing = NULL;         // Oldest ancestor of pindex which does not have BLOCK_HAVE_DATA.
    CBlockIndex* pindexFirstNotTreeValid = NULL;    // Oldest ancestor of pindex which does not have BLOCK_VALID_TREE (regardless of being valid or not).
    CBlockIndex* pindexFirstNotChainValid = NULL;   // Oldest ancestor of pindex which does not have BLOCK_VALID_CHAIN (regardless of being valid or not).
    CBlockIndex* pindexFirstNotScriptsValid = NULL; // Oldest ancestor of pindex which does not have BLOCK_VALID_SCRIPTS (regardless of being valid or not).
    while (pindex != NULL) {
        nNodes++;
        if (pindexFirstInvalid == NULL && pindex->nStatus & BLOCK_FAILED_VALID) pindexFirstInvalid = pindex;
        if (pindexFirstMissing == NULL && !(pindex->nStatus & BLOCK_HAVE_DATA)) pindexFirstMissing = pindex;
        if (pindex->pprev != NULL && pindexFirstNotTreeValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_TREE) pindexFirstNotTreeValid = pindex;
        if (pindex->pprev != NULL && pindexFirstNotChainValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_CHAIN) pindexFirstNotChainValid = pindex;
        if (pindex->pprev != NULL && pindexFirstNotScriptsValid == NULL && (pindex->nStatus & BLOCK_VALID_MASK) < BLOCK_VALID_SCRIPTS) pindexFirstNotScriptsValid = pindex;

        // Begin: actual consistency checks.
        if (pindex->pprev == NULL) {
            // Genesis block checks.
            assert(pindex->GetBlockHash() == Params().HashGenesisBlock()); // Genesis block's hash must match.
            assert(pindex == chainActive.Genesis());                       // The current active chain's genesis block must be this block.
        }
        // HAVE_DATA is equivalent to VALID_TRANSACTIONS and equivalent to nTx > 0 (we stored the number of transactions in the block)
        assert(!(pindex->nStatus & BLOCK_HAVE_DATA) == (pindex->nTx == 0));
        assert(((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TRANSACTIONS) == (pindex->nTx > 0));
        if (pindex->nChainTx == 0) assert(pindex->nSequenceId == 0); // nSequenceId can't be set for blocks that aren't linked
        // All parents having data is equivalent to all parents being VALID_TRANSACTIONS, which is equivalent to nChainTx being set.
        assert((pindexFirstMissing != NULL) == (pindex->nChainTx == 0));                                             // nChainTx == 0 is used to signal that all parent block's transaction data is available.
        assert(pindex->nHeight == nHeight);                                                                          // nHeight must be consistent.
        assert(pindex->pprev == NULL || pindex->nChainWork >= pindex->pprev->nChainWork);                            // For every block except the genesis block, the chainwork must be larger than the parent's.
        assert(nHeight < 2 || (pindex->pskip && (pindex->pskip->nHeight < nHeight)));                                // The pskip pointer must point back for all but the first 2 blocks.
        assert(pindexFirstNotTreeValid == NULL);                                                                     // All mapBlockIndex entries must at least be TREE valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_TREE) assert(pindexFirstNotTreeValid == NULL);       // TREE valid implies all parents are TREE valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_CHAIN) assert(pindexFirstNotChainValid == NULL);     // CHAIN valid implies all parents are CHAIN valid
        if ((pindex->nStatus & BLOCK_VALID_MASK) >= BLOCK_VALID_SCRIPTS) assert(pindexFirstNotScriptsValid == NULL); // SCRIPTS valid implies all parents are SCRIPTS valid
        if (pindexFirstInvalid == NULL) {
            // Checks for not-invalid blocks.
            assert((pindex->nStatus & BLOCK_FAILED_MASK) == 0); // The failed mask cannot be set for blocks without invalid parents.
        }
        if (!CBlockIndexWorkComparator()(pindex, chainActive.Tip()) && pindexFirstMissing == NULL) {
            if (pindexFirstInvalid == NULL) { // If this block sorts at least as good as the current tip and is valid, it must be in setBlockIndexCandidates.
                assert(setBlockIndexCandidates.count(pindex));
            }
        } else { // If this block sorts worse than the current tip, it cannot be in setBlockIndexCandidates.
            assert(setBlockIndexCandidates.count(pindex) == 0);
        }
        // Check whether this block is in mapBlocksUnlinked.
        std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangeUnlinked = mapBlocksUnlinked.equal_range(pindex->pprev);
        bool foundInUnlinked = false;
        while (rangeUnlinked.first != rangeUnlinked.second) {
            assert(rangeUnlinked.first->first == pindex->pprev);
            if (rangeUnlinked.first->second == pindex) {
                foundInUnlinked = true;
                break;
            }
            rangeUnlinked.first++;
        }
        if (pindex->pprev && pindex->nStatus & BLOCK_HAVE_DATA && pindexFirstMissing != NULL) {
            if (pindexFirstInvalid == NULL) { // If this block has block data available, some parent doesn't, and has no invalid parents, it must be in mapBlocksUnlinked.
                assert(foundInUnlinked);
            }
        } else { // If this block does not have block data available, or all parents do, it cannot be in mapBlocksUnlinked.
            assert(!foundInUnlinked);
        }
        // assert(pindex->GetBlockHash() == pindex->GetBlockHeader().GetHash()); // Perhaps too slow
        // End: actual consistency checks.

        // Try descending into the first subnode.
        std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> range = forward.equal_range(pindex);
        if (range.first != range.second) {
            // A subnode was found.
            pindex = range.first->second;
            nHeight++;
            continue;
        }
        // This is a leaf node.
        // Move upwards until we reach a node of which we have not yet visited the last child.
        while (pindex) {
            // We are going to either move to a parent or a sibling of pindex.
            // If pindex was the first with a certain property, unset the corresponding variable.
            if (pindex == pindexFirstInvalid) pindexFirstInvalid = NULL;
            if (pindex == pindexFirstMissing) pindexFirstMissing = NULL;
            if (pindex == pindexFirstNotTreeValid) pindexFirstNotTreeValid = NULL;
            if (pindex == pindexFirstNotChainValid) pindexFirstNotChainValid = NULL;
            if (pindex == pindexFirstNotScriptsValid) pindexFirstNotScriptsValid = NULL;
            // Find our parent.
            CBlockIndex* pindexPar = pindex->pprev;
            // Find which child we just visited.
            std::pair<std::multimap<CBlockIndex*, CBlockIndex*>::iterator, std::multimap<CBlockIndex*, CBlockIndex*>::iterator> rangePar = forward.equal_range(pindexPar);
            while (rangePar.first->second != pindex) {
                assert(rangePar.first != rangePar.second); // Our parent must have at least the node we're coming from as child.
                rangePar.first++;
            }
            // Proceed to the next one.
            rangePar.first++;
            if (rangePar.first != rangePar.second) {
                // Move to the sibling.
                pindex = rangePar.first->second;
                break;
            } else {
                // Move up further.
                pindex = pindexPar;
                nHeight--;
                continue;
            }
        }
    }

    // Check that we actually traversed the entire map.
    assert(nNodes == forward.size());
}

//////////////////////////////////////////////////////////////////////////////
//
// CAlert
//

string GetWarnings(string strFor)
{
    int nPriority = 0;
    string strStatusBar;
    string strRPC;

    if (!CLIENT_VERSION_IS_RELEASE)
        strStatusBar = _("This is a pre-release test build - use at your own risk - do not use for staking or merchant applications!");

    if (GetBoolArg("-testsafemode", false))
        strStatusBar = strRPC = "testsafemode enabled";

    // Misc warnings like out of disk space and clock is wrong
    if (strMiscWarning != "") {
        nPriority = 1000;
        strStatusBar = strMiscWarning;
    }

    if (fLargeWorkForkFound) {
        nPriority = 2000;
        strStatusBar = strRPC = _("Warning: The network does not appear to fully agree! Some miners appear to be experiencing issues.");
    } else if (fLargeWorkInvalidChainFound) {
        nPriority = 2000;
        strStatusBar = strRPC = _("Warning: We do not appear to fully agree with our peers! You may need to upgrade, or other nodes may need to upgrade.");
    }

    // Alerts
    {
        LOCK(cs_mapAlerts);
        BOOST_FOREACH (PAIRTYPE(const uint256, CAlert) & item, mapAlerts) {
            const CAlert& alert = item.second;
            if (alert.AppliesToMe() && alert.nPriority > nPriority) {
                nPriority = alert.nPriority;
                strStatusBar = alert.strStatusBar;
            }
        }
    }

    if (strFor == "statusbar")
        return strStatusBar;
    else if (strFor == "rpc")
        return strRPC;
    assert(!"GetWarnings() : invalid parameter");
    return "error";
}


//////////////////////////////////////////////////////////////////////////////
//
// Messages
//


bool static AlreadyHave(const CInv& inv)
{
    switch (inv.type) {
    case MSG_TX: {
        bool txInMap = false;
        txInMap = mempool.exists(inv.hash);
        return txInMap || mapOrphanTransactions.count(inv.hash) ||
               pcoinsTip->HaveCoins(inv.hash);
    }
    case MSG_DSTX:
        return mapObfuscationBroadcastTxes.count(inv.hash);
    case MSG_BLOCK:
        return mapBlockIndex.count(inv.hash);
    case MSG_TXLOCK_REQUEST:
        return mapTxLockReq.count(inv.hash) ||
               mapTxLockReqRejected.count(inv.hash);
    case MSG_TXLOCK_VOTE:
        return mapTxLockVote.count(inv.hash);
    case MSG_SPORK:
        return mapSporks.count(inv.hash);
    case MSG_MASTERNODE_WINNER:
        if (masternodePayments.mapMasternodePayeeVotes.count(inv.hash)) {
            masternodeSync.AddedMasternodeWinner(inv.hash);
            return true;
        }
        return false;
    case MSG_BUDGET_VOTE:
        if (budget.mapSeenMasternodeBudgetVotes.count(inv.hash)) {
            masternodeSync.AddedBudgetItem(inv.hash);
            return true;
        }
        return false;
    case MSG_BUDGET_PROPOSAL:
        if (budget.mapSeenMasternodeBudgetProposals.count(inv.hash)) {
            masternodeSync.AddedBudgetItem(inv.hash);
            return true;
        }
        return false;
    case MSG_BUDGET_FINALIZED_VOTE:
        if (budget.mapSeenFinalizedBudgetVotes.count(inv.hash)) {
            masternodeSync.AddedBudgetItem(inv.hash);
            return true;
        }
        return false;
    case MSG_BUDGET_FINALIZED:
        if (budget.mapSeenFinalizedBudgets.count(inv.hash)) {
            masternodeSync.AddedBudgetItem(inv.hash);
            return true;
        }
        return false;
    case MSG_MASTERNODE_ANNOUNCE:
        if (mnodeman.mapSeenMasternodeBroadcast.count(inv.hash)) {
            masternodeSync.AddedMasternodeList(inv.hash);
            return true;
        }
        return false;
    case MSG_MASTERNODE_PING:
        return mnodeman.mapSeenMasternodePing.count(inv.hash);
    }
    // Don't know what it is, just say we already got one
    return true;
}


void static ProcessGetData(CNode* pfrom)
{
    std::deque<CInv>::iterator it = pfrom->vRecvGetData.begin();

    vector<CInv> vNotFound;

    LOCK(cs_main);

    while (it != pfrom->vRecvGetData.end()) {
        // Don't bother if send buffer is too full to respond anyway
        if (pfrom->nSendSize >= SendBufferSize())
            break;

        const CInv& inv = *it;
        {
            boost::this_thread::interruption_point();
            it++;

            if (inv.type == MSG_BLOCK || inv.type == MSG_FILTERED_BLOCK) {
                bool send = false;
                BlockMap::iterator mi = mapBlockIndex.find(inv.hash);
                if (mi != mapBlockIndex.end()) {
                    if (chainActive.Contains(mi->second)) {
                        send = true;
                    } else {
                        // To prevent fingerprinting attacks, only send blocks outside of the active
                        // chain if they are valid, and no more than a max reorg depth than the best header
                        // chain we know about.
                        send = mi->second->IsValid(BLOCK_VALID_SCRIPTS) && (pindexBestHeader != NULL) &&
                               (chainActive.Height() - mi->second->nHeight < Params().MaxReorganizationDepth());
                        if (!send) {
                            LogPrintf("ProcessGetData(): ignoring request from peer=%i for old block that isn't in the main chain\n", pfrom->GetId());
                        }
                    }
                }
                if (send) {
                    // Send block from disk
                    CBlock block;
                    if (!ReadBlockFromDisk(block, (*mi).second))
                        assert(!"cannot load block from disk");
                    if (inv.type == MSG_BLOCK)
                        pfrom->PushMessage("block", block);
                    else // MSG_FILTERED_BLOCK)
                    {
                        LOCK(pfrom->cs_filter);
                        if (pfrom->pfilter) {
                            CMerkleBlock merkleBlock(block, *pfrom->pfilter);
                            pfrom->PushMessage("merkleblock", merkleBlock);
                            // CMerkleBlock just contains hashes, so also push any transactions in the block the client did not see
                            // This avoids hurting performance by pointlessly requiring a round-trip
                            // Note that there is currently no way for a node to request any single transactions we didnt send here -
                            // they must either disconnect and retry or request the full block.
                            // Thus, the protocol spec specified allows for us to provide duplicate txn here,
                            // however we MUST always provide at least what the remote peer needs
                            typedef std::pair<unsigned int, uint256> PairType;
                            BOOST_FOREACH (PairType& pair, merkleBlock.vMatchedTxn)
                                if (!pfrom->setInventoryKnown.count(CInv(MSG_TX, pair.second)))
                                    pfrom->PushMessage("tx", block.vtx[pair.first]);
                        }
                        // else
                        // no response
                    }

                    // Trigger them to send a getblocks request for the next batch of inventory
                    if (inv.hash == pfrom->hashContinue) {
                        // Bypass PushInventory, this must send even if redundant,
                        // and we want it right after the last block so they don't
                        // wait for other stuff first.
                        vector<CInv> vInv;
                        vInv.push_back(CInv(MSG_BLOCK, chainActive.Tip()->GetBlockHash()));
                        pfrom->PushMessage("inv", vInv);
                        pfrom->hashContinue = 0;
                    }
                }
            } else if (inv.IsKnownType()) {
                // Send stream from relay memory
                bool pushed = false;
                {
                    LOCK(cs_mapRelay);
                    map<CInv, CDataStream>::iterator mi = mapRelay.find(inv);
                    if (mi != mapRelay.end()) {
                        pfrom->PushMessage(inv.GetCommand(), (*mi).second);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_TX) {
                    CTransaction tx;
                    if (mempool.lookup(inv.hash, tx)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << tx;
                        pfrom->PushMessage("tx", ss);
                        pushed = true;
                    }
                }
                if (!pushed && inv.type == MSG_TXLOCK_VOTE) {
                    if (mapTxLockVote.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mapTxLockVote[inv.hash];
                        pfrom->PushMessage("txlvote", ss);
                        pushed = true;
                    }
                }
                if (!pushed && inv.type == MSG_TXLOCK_REQUEST) {
                    if (mapTxLockReq.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mapTxLockReq[inv.hash];
                        pfrom->PushMessage("ix", ss);
                        pushed = true;
                    }
                }
                if (!pushed && inv.type == MSG_SPORK) {
                    if (mapSporks.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mapSporks[inv.hash];
                        pfrom->PushMessage("spork", ss);
                        pushed = true;
                    }
                }
                if (!pushed && inv.type == MSG_MASTERNODE_WINNER) {
                    if (masternodePayments.mapMasternodePayeeVotes.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << masternodePayments.mapMasternodePayeeVotes[inv.hash];
                        pfrom->PushMessage("mnw", ss);
                        pushed = true;
                    }
                }
                if (!pushed && inv.type == MSG_BUDGET_VOTE) {
                    if (budget.mapSeenMasternodeBudgetVotes.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << budget.mapSeenMasternodeBudgetVotes[inv.hash];
                        pfrom->PushMessage("mvote", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_BUDGET_PROPOSAL) {
                    if (budget.mapSeenMasternodeBudgetProposals.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << budget.mapSeenMasternodeBudgetProposals[inv.hash];
                        pfrom->PushMessage("mprop", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_BUDGET_FINALIZED_VOTE) {
                    if (budget.mapSeenFinalizedBudgetVotes.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << budget.mapSeenFinalizedBudgetVotes[inv.hash];
                        pfrom->PushMessage("fbvote", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_BUDGET_FINALIZED) {
                    if (budget.mapSeenFinalizedBudgets.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << budget.mapSeenFinalizedBudgets[inv.hash];
                        pfrom->PushMessage("fbs", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_MASTERNODE_ANNOUNCE) {
                    if (mnodeman.mapSeenMasternodeBroadcast.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mnodeman.mapSeenMasternodeBroadcast[inv.hash];
                        pfrom->PushMessage("mnb", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_MASTERNODE_PING) {
                    if (mnodeman.mapSeenMasternodePing.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mnodeman.mapSeenMasternodePing[inv.hash];
                        pfrom->PushMessage("mnp", ss);
                        pushed = true;
                    }
                }

                if (!pushed && inv.type == MSG_DSTX) {
                    if (mapObfuscationBroadcastTxes.count(inv.hash)) {
                        CDataStream ss(SER_NETWORK, PROTOCOL_VERSION);
                        ss.reserve(1000);
                        ss << mapObfuscationBroadcastTxes[inv.hash].tx << mapObfuscationBroadcastTxes[inv.hash].vin << mapObfuscationBroadcastTxes[inv.hash].vchSig << mapObfuscationBroadcastTxes[inv.hash].sigTime;

                        pfrom->PushMessage("dstx", ss);
                        pushed = true;
                    }
                }


                if (!pushed) {
                    vNotFound.push_back(inv);
                }
            }

            // Track requests for our stuff.
            g_signals.Inventory(inv.hash);

            if (inv.type == MSG_BLOCK || inv.type == MSG_FILTERED_BLOCK)
                break;
        }
    }

    pfrom->vRecvGetData.erase(pfrom->vRecvGetData.begin(), it);

    if (!vNotFound.empty()) {
        // Let the peer know that we didn't find what it asked for, so it doesn't
        // have to wait around forever. Currently only SPV clients actually care
        // about this message: it's needed when they are recursively walking the
        // dependencies of relevant unconfirmed transactions. SPV clients want to
        // do that because they want to know about (and store and rebroadcast and
        // risk analyze) the dependencies of transactions relevant to them, without
        // having to download the entire memory pool.
        pfrom->PushMessage("notfound", vNotFound);
    }
}

bool static ProcessMessage(CNode* pfrom, string strCommand, CDataStream& vRecv, int64_t nTimeReceived)
{
    RandAddSeedPerfmon();
    if (fDebug)
        LogPrintf("received: %s (%u bytes) peer=%d\n", SanitizeString(strCommand), vRecv.size(), pfrom->id);
    if (mapArgs.count("-dropmessagestest") && GetRand(atoi(mapArgs["-dropmessagestest"])) == 0) {
        LogPrintf("dropmessagestest DROPPING RECV MESSAGE\n");
        return true;
    }

    if (strCommand == "version") {
        // Each connection can only send one version message
        if (pfrom->nVersion != 0) {
            pfrom->PushMessage("reject", strCommand, REJECT_DUPLICATE, string("Duplicate version message"));
            Misbehaving(pfrom->GetId(), 1);
            return false;
        }

        int64_t nTime;
        CAddress addrMe;
        CAddress addrFrom;
        uint64_t nNonce = 1;
        vRecv >> pfrom->nVersion >> pfrom->nServices >> nTime >> addrMe;
        if (pfrom->DisconnectOldProtocol(ActiveProtocol(), strCommand))
            return false;

        if (pfrom->nVersion == 10300)
            pfrom->nVersion = 300;
        if (!vRecv.empty())
            vRecv >> addrFrom >> nNonce;
        if (!vRecv.empty()) {
            vRecv >> LIMITED_STRING(pfrom->strSubVer, 256);
            pfrom->cleanSubVer = SanitizeString(pfrom->strSubVer);
        }
        if (!vRecv.empty())
            vRecv >> pfrom->nStartingHeight;
        if (!vRecv.empty())
            vRecv >> pfrom->fRelayTxes; // set to true after we get the first filter* message
        else
            pfrom->fRelayTxes = true;

        // Disconnect if we connected to ourself
        if (nNonce == nLocalHostNonce && nNonce > 1) {
            LogPrintf("connected to self at %s, disconnecting\n", pfrom->addr.ToString());
            pfrom->fDisconnect = true;
            return true;
        }

        pfrom->addrLocal = addrMe;
        if (pfrom->fInbound && addrMe.IsRoutable()) {
            SeenLocal(addrMe);
        }

        // Be shy and don't send version until we hear
        if (pfrom->fInbound)
            pfrom->PushVersion();

        pfrom->fClient = !(pfrom->nServices & NODE_NETWORK);

        // Potentially mark this peer as a preferred download peer.
        UpdatePreferredDownload(pfrom, State(pfrom->GetId()));

        // Change version
        pfrom->PushMessage("verack");
        pfrom->ssSend.SetVersion(min(pfrom->nVersion, PROTOCOL_VERSION));

        if (!pfrom->fInbound) {
            // Advertise our address
            if (fListen && !IsInitialBlockDownload()) {
                CAddress addr = GetLocalAddress(&pfrom->addr);
                if (addr.IsRoutable()) {
                    pfrom->PushAddress(addr);
                } else if (IsPeerAddrLocalGood(pfrom)) {
                    addr.SetIP(pfrom->addrLocal);
                    pfrom->PushAddress(addr);
                }
            }

            // Get recent addresses
            if (pfrom->fOneShot || pfrom->nVersion >= CADDR_TIME_VERSION || addrman.size() < 1000) {
                pfrom->PushMessage("getaddr");
                pfrom->fGetAddr = true;
            }
            addrman.Good(pfrom->addr);
        } else {
            if (((CNetAddr)pfrom->addr) == (CNetAddr)addrFrom) {
                addrman.Add(addrFrom, addrFrom);
                addrman.Good(addrFrom);
            }
        }

        // Relay alerts
        {
            LOCK(cs_mapAlerts);
            BOOST_FOREACH (PAIRTYPE(const uint256, CAlert) & item, mapAlerts)
                item.second.RelayTo(pfrom);
        }

        pfrom->fSuccessfullyConnected = true;

        string remoteAddr;
        if (fLogIPs)
            remoteAddr = ", peeraddr=" + pfrom->addr.ToString();

        LogPrintf("receive version message: %s: version %d, blocks=%d, us=%s, peer=%d%s\n",
            pfrom->cleanSubVer, pfrom->nVersion,
            pfrom->nStartingHeight, addrMe.ToString(), pfrom->id,
            remoteAddr);

        AddTimeData(pfrom->addr, nTime);
    }


    else if (pfrom->nVersion == 0) {
        // Must have a version message before anything else
        Misbehaving(pfrom->GetId(), 1);
        return false;
    }


    else if (strCommand == "verack") {
        pfrom->SetRecvVersion(min(pfrom->nVersion, PROTOCOL_VERSION));

        // Mark this node as currently connected, so we update its timestamp later.
        if (pfrom->fNetworkNode) {
            LOCK(cs_main);
            State(pfrom->GetId())->fCurrentlyConnected = true;
        }
    }


    else if (strCommand == "addr") {
        vector<CAddress> vAddr;
        vRecv >> vAddr;

        // Don't want addr from older versions unless seeding
        if (pfrom->nVersion < CADDR_TIME_VERSION && addrman.size() > 1000)
            return true;
        if (vAddr.size() > 1000) {
            Misbehaving(pfrom->GetId(), 20);
            return error("message addr size() = %u", vAddr.size());
        }

        // Store the new addresses
        vector<CAddress> vAddrOk;
        int64_t nNow = GetAdjustedTime();
        int64_t nSince = nNow - 10 * 60;
        BOOST_FOREACH (CAddress& addr, vAddr) {
            boost::this_thread::interruption_point();

            if (addr.nTime <= 100000000 || addr.nTime > nNow + 10 * 60)
                addr.nTime = nNow - 5 * 24 * 60 * 60;
            pfrom->AddAddressKnown(addr);
            bool fReachable = IsReachable(addr);
            if (addr.nTime > nSince && !pfrom->fGetAddr && vAddr.size() <= 10 && addr.IsRoutable()) {
                // Relay to a limited number of other nodes
                {
                    LOCK(cs_vNodes);
                    // Use deterministic randomness to send to the same nodes for 24 hours
                    // at a time so the setAddrKnowns of the chosen nodes prevent repeats
                    static uint256 hashSalt;
                    if (hashSalt == 0)
                        hashSalt = GetRandHash();
                    uint64_t hashAddr = addr.GetHash();
                    uint256 hashRand = hashSalt ^ (hashAddr << 32) ^ ((GetTime() + hashAddr) / (24 * 60 * 60));
                    hashRand = Hash(BEGIN(hashRand), END(hashRand));
                    multimap<uint256, CNode*> mapMix;
                    BOOST_FOREACH (CNode* pnode, vNodes) {
                        if (pnode->nVersion < CADDR_TIME_VERSION)
                            continue;
                        unsigned int nPointer;
                        memcpy(&nPointer, &pnode, sizeof(nPointer));
                        uint256 hashKey = hashRand ^ nPointer;
                        hashKey = Hash(BEGIN(hashKey), END(hashKey));
                        mapMix.insert(make_pair(hashKey, pnode));
                    }
                    int nRelayNodes = fReachable ? 2 : 1; // limited relaying of addresses outside our network(s)
                    for (multimap<uint256, CNode*>::iterator mi = mapMix.begin(); mi != mapMix.end() && nRelayNodes-- > 0; ++mi)
                        ((*mi).second)->PushAddress(addr);
                }
            }
            // Do not store addresses outside our network
            if (fReachable)
                vAddrOk.push_back(addr);
        }
        addrman.Add(vAddrOk, pfrom->addr, 2 * 60 * 60);
        if (vAddr.size() < 1000)
            pfrom->fGetAddr = false;
        if (pfrom->fOneShot)
            pfrom->fDisconnect = true;
    }


    else if (strCommand == "inv") {
        vector<CInv> vInv;
        vRecv >> vInv;
        if (vInv.size() > MAX_INV_SZ) {
            Misbehaving(pfrom->GetId(), 20);
            return error("message inv size() = %u", vInv.size());
        }

        LOCK(cs_main);

        std::vector<CInv> vToFetch;

        for (unsigned int nInv = 0; nInv < vInv.size(); nInv++) {
            const CInv& inv = vInv[nInv];

            boost::this_thread::interruption_point();
            pfrom->AddInventoryKnown(inv);

            bool fAlreadyHave = AlreadyHave(inv);
            LogPrint("net", "got inv: %s  %s peer=%d\n", inv.ToString(), fAlreadyHave ? "have" : "new", pfrom->id);

            if (!fAlreadyHave && !fImporting && !fReindex && inv.type != MSG_BLOCK)
                pfrom->AskFor(inv);


            if (inv.type == MSG_BLOCK) {
                UpdateBlockAvailability(pfrom->GetId(), inv.hash);
                if (!fAlreadyHave && !fImporting && !fReindex && !mapBlocksInFlight.count(inv.hash)) {
                    // Add this to the list of blocks to request
                    vToFetch.push_back(inv);
                    LogPrint("net", "getblocks (%d) %s to peer=%d\n", pindexBestHeader->nHeight, inv.hash.ToString(), pfrom->id);
                }
            }

            // Track requests for our stuff
            g_signals.Inventory(inv.hash);

            if (pfrom->nSendSize > (SendBufferSize() * 2)) {
                Misbehaving(pfrom->GetId(), 50);
                return error("send buffer size() = %u", pfrom->nSendSize);
            }
        }

        if (!vToFetch.empty())
            pfrom->PushMessage("getdata", vToFetch);
    }


    else if (strCommand == "getdata") {
        vector<CInv> vInv;
        vRecv >> vInv;
        if (vInv.size() > MAX_INV_SZ) {
            Misbehaving(pfrom->GetId(), 20);
            return error("message getdata size() = %u", vInv.size());
        }

        if (fDebug || (vInv.size() != 1))
            LogPrint("net", "received getdata (%u invsz) peer=%d\n", vInv.size(), pfrom->id);

        if ((fDebug && vInv.size() > 0) || (vInv.size() == 1))
            LogPrint("net", "received getdata for: %s peer=%d\n", vInv[0].ToString(), pfrom->id);

        pfrom->vRecvGetData.insert(pfrom->vRecvGetData.end(), vInv.begin(), vInv.end());
        ProcessGetData(pfrom);
    }


    else if (strCommand == "getblocks" || strCommand == "getheaders") {
        CBlockLocator locator;
        uint256 hashStop;
        vRecv >> locator >> hashStop;

        LOCK(cs_main);

        // Find the last block the caller has in the main chain
        CBlockIndex* pindex = FindForkInGlobalIndex(chainActive, locator);

        // Send the rest of the chain
        if (pindex)
            pindex = chainActive.Next(pindex);
        int nLimit = 500;
        LogPrintf("getblocks %d to %s limit %d from peer=%d\n", (pindex ? pindex->nHeight : -1), hashStop == uint256(0) ? "end" : hashStop.ToString(), nLimit, pfrom->id);
        for (; pindex; pindex = chainActive.Next(pindex)) {
            if (pindex->GetBlockHash() == hashStop) {
                LogPrint("net", "  getblocks stopping at %d %s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                break;
            }
            pfrom->PushInventory(CInv(MSG_BLOCK, pindex->GetBlockHash()));
            if (--nLimit <= 0) {
                // When this block is requested, we'll send an inv that'll make them
                // getblocks the next batch of inventory.
                LogPrint("net", "  getblocks stopping at limit %d %s\n", pindex->nHeight, pindex->GetBlockHash().ToString());
                pfrom->hashContinue = pindex->GetBlockHash();
                break;
            }
        }
    }


    else if (strCommand == "headers" && Params().HeadersFirstSyncingActive()) {
        CBlockLocator locator;
        uint256 hashStop;
        vRecv >> locator >> hashStop;

        LOCK(cs_main);

        if (IsInitialBlockDownload())
            return true;

        CBlockIndex* pindex = NULL;
        if (locator.IsNull()) {
            // If locator is null, return the hashStop block
            BlockMap::iterator mi = mapBlockIndex.find(hashStop);
            if (mi == mapBlockIndex.end())
                return true;
            pindex = (*mi).second;
        } else {
            // Find the last block the caller has in the main chain
            pindex = FindForkInGlobalIndex(chainActive, locator);
            if (pindex)
                pindex = chainActive.Next(pindex);
        }

        // we must use CBlocks, as CBlockHeaders won't include the 0x00 nTx count at the end
        vector<CBlock> vHeaders;
        int nLimit = MAX_HEADERS_RESULTS;
        if (fDebug)
            LogPrintf("getheaders %d to %s from peer=%d\n", (pindex ? pindex->nHeight : -1), hashStop.ToString(), pfrom->id);
        for (; pindex; pindex = chainActive.Next(pindex)) {
            vHeaders.push_back(pindex->GetBlockHeader());
            if (--nLimit <= 0 || pindex->GetBlockHash() == hashStop)
                break;
        }
        pfrom->PushMessage("headers", vHeaders);
    }


    else if (strCommand == "tx" || strCommand == "dstx") {
        vector<uint256> vWorkQueue;
        vector<uint256> vEraseQueue;
        CTransaction tx;

        //masternode signed transaction
        bool ignoreFees = false;
        CTxIn vin;
        vector<unsigned char> vchSig;
        int64_t sigTime;

        if (strCommand == "tx") {
            vRecv >> tx;
        } else if (strCommand == "dstx") {
            //these allow masternodes to publish a limited amount of free transactions
            vRecv >> tx >> vin >> vchSig >> sigTime;

            CMasternode* pmn = mnodeman.Find(vin);
            if (pmn != NULL) {
                if (!pmn->allowFreeTx) {
                    //multiple peers can send us a valid masternode transaction
                    if (fDebug) LogPrintf("dstx: Masternode sending too many transactions %s\n", tx.GetHash().ToString());
                    return true;
                }

                std::string strMessage = tx.GetHash().ToString() + boost::lexical_cast<std::string>(sigTime);

                std::string errorMessage = "";
                if (!obfuScationSigner.VerifyMessage(pmn->pubKeyMasternode, vchSig, strMessage, errorMessage)) {
                    LogPrintf("dstx: Got bad masternode address signature %s \n", vin.ToString());
                    //pfrom->Misbehaving(20);
                    return false;
                }

                LogPrintf("dstx: Got Masternode transaction %s\n", tx.GetHash().ToString());

                ignoreFees = true;
                pmn->allowFreeTx = false;

                if (!mapObfuscationBroadcastTxes.count(tx.GetHash())) {
                    CObfuscationBroadcastTx dstx;
                    dstx.tx = tx;
                    dstx.vin = vin;
                    dstx.vchSig = vchSig;
                    dstx.sigTime = sigTime;

                    mapObfuscationBroadcastTxes.insert(make_pair(tx.GetHash(), dstx));
                }
            }
        }

        CInv inv(MSG_TX, tx.GetHash());
        pfrom->AddInventoryKnown(inv);

        LOCK(cs_main);

        bool fMissingInputs = false;
        CValidationState state;

        mapAlreadyAskedFor.erase(inv);

        if (AcceptToMemoryPool(mempool, state, tx, true, &fMissingInputs, false, ignoreFees)) {
            mempool.check(pcoinsTip);
            RelayTransaction(tx);
            vWorkQueue.push_back(inv.hash);

            LogPrint("mempool", "AcceptToMemoryPool: peer=%d %s : accepted %s (poolsz %u)\n",
                pfrom->id, pfrom->cleanSubVer,
                tx.GetHash().ToString(),
                mempool.mapTx.size());

            // Recursively process any orphan transactions that depended on this one
            set<NodeId> setMisbehaving;
            for (unsigned int i = 0; i < vWorkQueue.size(); i++) {
                map<uint256, set<uint256> >::iterator itByPrev = mapOrphanTransactionsByPrev.find(vWorkQueue[i]);
                if (itByPrev == mapOrphanTransactionsByPrev.end())
                    continue;
                for (set<uint256>::iterator mi = itByPrev->second.begin();
                     mi != itByPrev->second.end();
                     ++mi) {
                    const uint256& orphanHash = *mi;
                    const CTransaction& orphanTx = mapOrphanTransactions[orphanHash].tx;
                    NodeId fromPeer = mapOrphanTransactions[orphanHash].fromPeer;
                    bool fMissingInputs2 = false;
                    // Use a dummy CValidationState so someone can't setup nodes to counter-DoS based on orphan
                    // resolution (that is, feeding people an invalid transaction based on LegitTxX in order to get
                    // anyone relaying LegitTxX banned)
                    CValidationState stateDummy;


                    if (setMisbehaving.count(fromPeer))
                        continue;
                    if (AcceptToMemoryPool(mempool, stateDummy, orphanTx, true, &fMissingInputs2)) {
                        LogPrint("mempool", "   accepted orphan tx %s\n", orphanHash.ToString());
                        RelayTransaction(orphanTx);
                        vWorkQueue.push_back(orphanHash);
                        vEraseQueue.push_back(orphanHash);
                    } else if (!fMissingInputs2) {
                        int nDos = 0;
                        if (stateDummy.IsInvalid(nDos) && nDos > 0) {
                            // Punish peer that gave us an invalid orphan tx
                            Misbehaving(fromPeer, nDos);
                            setMisbehaving.insert(fromPeer);
                            LogPrint("mempool", "   invalid orphan tx %s\n", orphanHash.ToString());
                        }
                        // Has inputs but not accepted to mempool
                        // Probably non-standard or insufficient fee/priority
                        LogPrint("mempool", "   removed orphan tx %s\n", orphanHash.ToString());
                        vEraseQueue.push_back(orphanHash);
                    }
                    mempool.check(pcoinsTip);
                }
            }

            BOOST_FOREACH (uint256 hash, vEraseQueue)
                EraseOrphanTx(hash);
        } else if (fMissingInputs) {
            AddOrphanTx(tx, pfrom->GetId());

            // DoS prevention: do not allow mapOrphanTransactions to grow unbounded
            unsigned int nMaxOrphanTx = (unsigned int)std::max((int64_t)0, GetArg("-maxorphantx", DEFAULT_MAX_ORPHAN_TRANSACTIONS));
            unsigned int nEvicted = LimitOrphanTxSize(nMaxOrphanTx);
            if (nEvicted > 0)
                LogPrint("mempool", "mapOrphan overflow, removed %u tx\n", nEvicted);
        } else if (pfrom->fWhitelisted) {
            // Always relay transactions received from whitelisted peers, even
            // if they are already in the mempool (allowing the node to function
            // as a gateway for nodes hidden behind it).

            RelayTransaction(tx);
        }

        if (strCommand == "dstx") {
            CInv inv(MSG_DSTX, tx.GetHash());
            RelayInv(inv);
        }

        int nDoS = 0;
        if (state.IsInvalid(nDoS)) {
            LogPrint("mempool", "%s from peer=%d %s was not accepted into the memory pool: %s\n", tx.GetHash().ToString(),
                pfrom->id, pfrom->cleanSubVer,
                state.GetRejectReason());
            pfrom->PushMessage("reject", strCommand, state.GetRejectCode(),
                state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), inv.hash);
            if (nDoS > 0)
                Misbehaving(pfrom->GetId(), nDoS);
        }
    }


    else if (strCommand == "headers" && Params().HeadersFirstSyncingActive() && !fImporting && !fReindex) // Ignore headers received while importing
    {
        std::vector<CBlockHeader> headers;

        // Bypass the normal CBlock deserialization, as we don't want to risk deserializing 2000 full blocks.
        unsigned int nCount = ReadCompactSize(vRecv);
        if (nCount > MAX_HEADERS_RESULTS) {
            Misbehaving(pfrom->GetId(), 20);
            return error("headers message size = %u", nCount);
        }
        headers.resize(nCount);
        for (unsigned int n = 0; n < nCount; n++) {
            vRecv >> headers[n];
            ReadCompactSize(vRecv); // ignore tx count; assume it is 0.
        }

        LOCK(cs_main);

        if (nCount == 0) {
            // Nothing interesting. Stop asking this peers for more headers.
            return true;
        }
        CBlockIndex* pindexLast = NULL;
        BOOST_FOREACH (const CBlockHeader& header, headers) {
            CValidationState state;
            if (pindexLast != NULL && header.hashPrevBlock != pindexLast->GetBlockHash()) {
                Misbehaving(pfrom->GetId(), 20);
                return error("non-continuous headers sequence");
            }

            /*TODO: this has a CBlock cast on it so that it will compile. There should be a solution for this
             * before headers are reimplemented on mainnet
             */
            if (!AcceptBlockHeader((CBlock)header, state, &pindexLast)) {
                int nDoS;
                if (state.IsInvalid(nDoS)) {
                    if (nDoS > 0)
                        Misbehaving(pfrom->GetId(), nDoS);
                    std::string strError = "invalid header received " + header.GetHash().ToString();
                    return error(strError.c_str());
                }
            }
        }

        if (pindexLast)
            UpdateBlockAvailability(pfrom->GetId(), pindexLast->GetBlockHash());

        if (nCount == MAX_HEADERS_RESULTS && pindexLast) {
            // Headers message had its maximum size; the peer may have more headers.
            // TODO: optimize: if pindexLast is an ancestor of chainActive.Tip or pindexBestHeader, continue
            // from there instead.
            LogPrintf("more getheaders (%d) to end to peer=%d (startheight:%d)\n", pindexLast->nHeight, pfrom->id, pfrom->nStartingHeight);
            pfrom->PushMessage("getheaders", chainActive.GetLocator(pindexLast), uint256(0));
        }

        CheckBlockIndex();
    }

    else if (strCommand == "block" && !fImporting && !fReindex) // Ignore blocks received while importing
    {
        CBlock block;
        vRecv >> block;
        uint256 hashBlock = block.GetHash();
        CInv inv(MSG_BLOCK, hashBlock);
        LogPrint("net", "received block %s peer=%d\n", inv.hash.ToString(), pfrom->id);

        //sometimes we will be sent their most recent block and its not the one we want, in that case tell where we are
        if (!mapBlockIndex.count(block.hashPrevBlock)) {
            if (find(pfrom->vBlockRequested.begin(), pfrom->vBlockRequested.end(), hashBlock) != pfrom->vBlockRequested.end()) {
                //we already asked for this block, so lets work backwards and ask for the previous block
                pfrom->PushMessage("getblocks", chainActive.GetLocator(), block.hashPrevBlock);
                pfrom->vBlockRequested.push_back(block.hashPrevBlock);
            } else {
                //ask to sync to this block
                pfrom->PushMessage("getblocks", chainActive.GetLocator(), hashBlock);
                pfrom->vBlockRequested.push_back(hashBlock);
            }
        } else {
            pfrom->AddInventoryKnown(inv);

            CValidationState state;
            ProcessNewBlock(state, pfrom, &block);
            int nDoS;
            if (state.IsInvalid(nDoS)) {
                pfrom->PushMessage("reject", strCommand, state.GetRejectCode(),
                    state.GetRejectReason().substr(0, MAX_REJECT_MESSAGE_LENGTH), inv.hash);
                if (nDoS > 0) {
                    TRY_LOCK(cs_main, lockMain);
                    if (lockMain) Misbehaving(pfrom->GetId(), nDoS);
                }

                //disconnect this node if its old protocol version
                pfrom->DisconnectOldProtocol(ActiveProtocol(), strCommand);
            }
        }

    }


    // This asymmetric behavior for inbound and outbound connections was introduced
    // to prevent a fingerprinting attack: an attacker can send specific fake addresses
    // to users' AddrMan and later request them by sending getaddr messages.
    // Making users (which are behind NAT and can only make outgoing connections) ignore
    // getaddr message mitigates the attack.
    else if ((strCommand == "getaddr") && (pfrom->fInbound)) {
        pfrom->vAddrToSend.clear();
        vector<CAddress> vAddr = addrman.GetAddr();
        BOOST_FOREACH (const CAddress& addr, vAddr)
            pfrom->PushAddress(addr);
    }


    else if (strCommand == "mempool") {
        LOCK2(cs_main, pfrom->cs_filter);

        std::vector<uint256> vtxid;
        mempool.queryHashes(vtxid);
        vector<CInv> vInv;
        BOOST_FOREACH (uint256& hash, vtxid) {
            CInv inv(MSG_TX, hash);
            CTransaction tx;
            bool fInMemPool = mempool.lookup(hash, tx);
            if (!fInMemPool) continue; // another thread removed since queryHashes, maybe...
            if ((pfrom->pfilter && pfrom->pfilter->IsRelevantAndUpdate(tx)) ||
                (!pfrom->pfilter))
                vInv.push_back(inv);
            if (vInv.size() == MAX_INV_SZ) {
                pfrom->PushMessage("inv", vInv);
                vInv.clear();
            }
        }
        if (vInv.size() > 0)
            pfrom->PushMessage("inv", vInv);
    }


    else if (strCommand == "ping") {
        if (pfrom->nVersion > BIP0031_VERSION) {
            uint64_t nonce = 0;
            vRecv >> nonce;
            // Echo the message back with the nonce. This allows for two useful features:
            //
            // 1) A remote node can quickly check if the connection is operational
            // 2) Remote nodes can measure the latency of the network thread. If this node
            //    is overloaded it won't respond to pings quickly and the remote node can
            //    avoid sending us more work, like chain download requests.
            //
            // The nonce stops the remote getting confused between different pings: without
            // it, if the remote node sends a ping once per second and this node takes 5
            // seconds to respond to each, the 5th ping the remote sends would appear to
            // return very quickly.
            pfrom->PushMessage("pong", nonce);
        }
    }


    else if (strCommand == "pong") {
        int64_t pingUsecEnd = nTimeReceived;
        uint64_t nonce = 0;
        size_t nAvail = vRecv.in_avail();
        bool bPingFinished = false;
        std::string sProblem;

        if (nAvail >= sizeof(nonce)) {
            vRecv >> nonce;

            // Only process pong message if there is an outstanding ping (old ping without nonce should never pong)
            if (pfrom->nPingNonceSent != 0) {
                if (nonce == pfrom->nPingNonceSent) {
                    // Matching pong received, this ping is no longer outstanding
                    bPingFinished = true;
                    int64_t pingUsecTime = pingUsecEnd - pfrom->nPingUsecStart;
                    if (pingUsecTime > 0) {
                        // Successful ping time measurement, replace previous
                        pfrom->nPingUsecTime = pingUsecTime;
                    } else {
                        // This should never happen
                        sProblem = "Timing mishap";
                    }
                } else {
                    // Nonce mismatches are normal when pings are overlapping
                    sProblem = "Nonce mismatch";
                    if (nonce == 0) {
                        // This is most likely a bug in another implementation somewhere, cancel this ping
                        bPingFinished = true;
                        sProblem = "Nonce zero";
                    }
                }
            } else {
                sProblem = "Unsolicited pong without ping";
            }
        } else {
            // This is most likely a bug in another implementation somewhere, cancel this ping
            bPingFinished = true;
            sProblem = "Short payload";
        }

        if (!(sProblem.empty())) {
            LogPrint("net", "pong peer=%d %s: %s, %x expected, %x received, %u bytes\n",
                pfrom->id,
                pfrom->cleanSubVer,
                sProblem,
                pfrom->nPingNonceSent,
                nonce,
                nAvail);
        }
        if (bPingFinished) {
            pfrom->nPingNonceSent = 0;
        }
    }


    else if (fAlerts && strCommand == "alert") {
        CAlert alert;
        vRecv >> alert;

        uint256 alertHash = alert.GetHash();
        if (pfrom->setKnown.count(alertHash) == 0) {
            if (alert.ProcessAlert()) {
                // Relay
                pfrom->setKnown.insert(alertHash);
                {
                    LOCK(cs_vNodes);
                    BOOST_FOREACH (CNode* pnode, vNodes)
                        alert.RelayTo(pnode);
                }
            } else {
                // Small DoS penalty so peers that send us lots of
                // duplicate/expired/invalid-signature/whatever alerts
                // eventually get banned.
                // This isn't a Misbehaving(100) (immediate ban) because the
                // peer might be an older or different implementation with
                // a different signature key, etc.
                Misbehaving(pfrom->GetId(), 10);
            }
        }
    }

    else if (!(nLocalServices & NODE_BLOOM) &&
             (strCommand == "filterload" ||
                 strCommand == "filteradd" ||
                 strCommand == "filterclear")) {
        LogPrintf("bloom message=%s\n", strCommand);
        Misbehaving(pfrom->GetId(), 100);
    }

    else if (strCommand == "filterload") {
        CBloomFilter filter;
        vRecv >> filter;

        if (!filter.IsWithinSizeConstraints())
            // There is no excuse for sending a too-large filter
            Misbehaving(pfrom->GetId(), 100);
        else {
            LOCK(pfrom->cs_filter);
            delete pfrom->pfilter;
            pfrom->pfilter = new CBloomFilter(filter);
            pfrom->pfilter->UpdateEmptyFull();
        }
        pfrom->fRelayTxes = true;
    }


    else if (strCommand == "filteradd") {
        vector<unsigned char> vData;
        vRecv >> vData;

        // Nodes must NEVER send a data item > 520 bytes (the max size for a script data object,
        // and thus, the maximum size any matched object can have) in a filteradd message
        if (vData.size() > MAX_SCRIPT_ELEMENT_SIZE) {
            Misbehaving(pfrom->GetId(), 100);
        } else {
            LOCK(pfrom->cs_filter);
            if (pfrom->pfilter)
                pfrom->pfilter->insert(vData);
            else
                Misbehaving(pfrom->GetId(), 100);
        }
    }


    else if (strCommand == "filterclear") {
        LOCK(pfrom->cs_filter);
        delete pfrom->pfilter;
        pfrom->pfilter = new CBloomFilter();
        pfrom->fRelayTxes = true;
    }


    else if (strCommand == "reject") {
        if (fDebug) {
            try {
                string strMsg;
                unsigned char ccode;
                string strReason;
                vRecv >> LIMITED_STRING(strMsg, CMessageHeader::COMMAND_SIZE) >> ccode >> LIMITED_STRING(strReason, MAX_REJECT_MESSAGE_LENGTH);

                ostringstream ss;
                ss << strMsg << " code " << itostr(ccode) << ": " << strReason;

                if (strMsg == "block" || strMsg == "tx") {
                    uint256 hash;
                    vRecv >> hash;
                    ss << ": hash " << hash.ToString();
                }
                LogPrint("net", "Reject %s\n", SanitizeString(ss.str()));
            } catch (std::ios_base::failure& e) {
                // Avoid feedback loops by preventing reject messages from triggering a new reject message.
                LogPrint("net", "Unparseable reject message received\n");
            }
        }
    } else {
        //probably one the extensions
        obfuScationPool.ProcessMessageObfuscation(pfrom, strCommand, vRecv);
        mnodeman.ProcessMessage(pfrom, strCommand, vRecv);
        budget.ProcessMessage(pfrom, strCommand, vRecv);
        masternodePayments.ProcessMessageMasternodePayments(pfrom, strCommand, vRecv);
        ProcessMessageSwiftTX(pfrom, strCommand, vRecv);
        ProcessSpork(pfrom, strCommand, vRecv);
        masternodeSync.ProcessMessage(pfrom, strCommand, vRecv);
    }


    return true;
}

// Note: whenever a protocol update is needed toggle between both implementations (comment out the formerly active one)
//       so we can leave the existing clients untouched (old SPORK will stay on so they don't see even older clients). 
//       Those old clients won't react to the changes of the other (new) SPORK because at the time of their implementation
//       it was the one which was commented out
int ActiveProtocol()
{

    // SPORK_14 was used for 70710. Leave it 'ON' so they don't see < 70710 nodes. They won't react to SPORK_15
    // messages because it's not in their code
/*
    if (IsSporkActive(SPORK_14_NEW_PROTOCOL_ENFORCEMENT)) {
        if (chainActive.Tip()->nHeight >= Params().ModifierUpgradeBlock())
            return MIN_PEER_PROTO_VERSION_AFTER_ENFORCEMENT;
    }

    return MIN_PEER_PROTO_VERSION_BEFORE_ENFORCEMENT;
*/


    // SPORK_15 is used for 70910. Nodes < 70910 don't see it and still get their protocol version via SPORK_14 and their 
    // own ModifierUpgradeBlock()
 /*
    if (IsSporkActive(SPORK_15_NEW_PROTOCOL_ENFORCEMENT_2))
            return MIN_PEER_PROTO_VERSION_AFTER_ENFORCEMENT;

    return MIN_PEER_PROTO_VERSION_BEFORE_ENFORCEMENT;
	*/
	// This spork is to fix the exploit listed here. https://medium.com/@dsl_uiuc/fake-stake-attacks-on-chain-based-proof-of-stake-cryptocurrencies-b8b05723f806
	if (IsSporkActive(SPORK_17_NEW_PROTOCOL_ENFORCEMENT_3))
		return MIN_PEER_PROTO_VERSION_AFTER_ENFORCEMENT;

	return MIN_PEER_PROTO_VERSION_BEFORE_ENFORCEMENT;
}

// requires LOCK(cs_vRecvMsg)
bool ProcessMessages(CNode* pfrom)
{
    //if (fDebug)
    //    LogPrintf("ProcessMessages(%u messages)\n", pfrom->vRecvMsg.size());

    //
    // Message format
    //  (4) message start
    //  (12) command
    //  (4) size
    //  (4) checksum
    //  (x) data
    //
    bool fOk = true;

    if (!pfrom->vRecvGetData.empty())
        ProcessGetData(pfrom);

    // this maintains the order of responses
    if (!pfrom->vRecvGetData.empty()) return fOk;

    std::deque<CNetMessage>::iterator it = pfrom->vRecvMsg.begin();
    while (!pfrom->fDisconnect && it != pfrom->vRecvMsg.end()) {
        // Don't bother if send buffer is too full to respond anyway
        if (pfrom->nSendSize >= SendBufferSize())
            break;

        // get next message
        CNetMessage& msg = *it;

        //if (fDebug)
        //    LogPrintf("ProcessMessages(message %u msgsz, %u bytes, complete:%s)\n",
        //            msg.hdr.nMessageSize, msg.vRecv.size(),
        //            msg.complete() ? "Y" : "N");

        // end, if an incomplete message is found
        if (!msg.complete())
            break;

        // at this point, any failure means we can delete the current message
        it++;

        // Scan for message start
        if (memcmp(msg.hdr.pchMessageStart, Params().MessageStart(), MESSAGE_START_SIZE) != 0) {
            LogPrintf("PROCESSMESSAGE: INVALID MESSAGESTART %s peer=%d\n", SanitizeString(msg.hdr.GetCommand()), pfrom->id);
            fOk = false;
            break;
        }

        // Read header
        CMessageHeader& hdr = msg.hdr;
        if (!hdr.IsValid()) {
            LogPrintf("PROCESSMESSAGE: ERRORS IN HEADER %s peer=%d\n", SanitizeString(hdr.GetCommand()), pfrom->id);
            continue;
        }
        string strCommand = hdr.GetCommand();

        // Message size
        unsigned int nMessageSize = hdr.nMessageSize;

        // Checksum
        CDataStream& vRecv = msg.vRecv;
        uint256 hash = Hash(vRecv.begin(), vRecv.begin() + nMessageSize);
        unsigned int nChecksum = 0;
        memcpy(&nChecksum, &hash, sizeof(nChecksum));
        if (nChecksum != hdr.nChecksum) {
            LogPrintf("ProcessMessages(%s, %u bytes): CHECKSUM ERROR nChecksum=%08x hdr.nChecksum=%08x\n",
                SanitizeString(strCommand), nMessageSize, nChecksum, hdr.nChecksum);
            continue;
        }

        // Process message
        bool fRet = false;
        try {
            fRet = ProcessMessage(pfrom, strCommand, vRecv, msg.nTime);
            boost::this_thread::interruption_point();
        } catch (std::ios_base::failure& e) {
            pfrom->PushMessage("reject", strCommand, REJECT_MALFORMED, string("error parsing message"));
            if (strstr(e.what(), "end of data")) {
                // Allow exceptions from under-length message on vRecv
                LogPrintf("ProcessMessages(%s, %u bytes): Exception '%s' caught, normally caused by a message being shorter than its stated length\n", SanitizeString(strCommand), nMessageSize, e.what());
            } else if (strstr(e.what(), "size too large")) {
                // Allow exceptions from over-long size
                LogPrintf("ProcessMessages(%s, %u bytes): Exception '%s' caught\n", SanitizeString(strCommand), nMessageSize, e.what());
            } else {
                PrintExceptionContinue(&e, "ProcessMessages()");
            }
        } catch (boost::thread_interrupted) {
            throw;
        } catch (std::exception& e) {
            PrintExceptionContinue(&e, "ProcessMessages()");
        } catch (...) {
            PrintExceptionContinue(NULL, "ProcessMessages()");
        }

        if (!fRet)
            LogPrintf("ProcessMessage(%s, %u bytes) FAILED peer=%d\n", SanitizeString(strCommand), nMessageSize, pfrom->id);

        break;
    }

    // In case the connection got shut down, its receive buffer was wiped
    if (!pfrom->fDisconnect)
        pfrom->vRecvMsg.erase(pfrom->vRecvMsg.begin(), it);

    return fOk;
}


bool SendMessages(CNode* pto, bool fSendTrickle)
{
    {
        // Don't send anything until we get their version message
        if (pto->nVersion == 0)
            return true;

        //
        // Message: ping
        //
        bool pingSend = false;
        if (pto->fPingQueued) {
            // RPC ping request by user
            pingSend = true;
        }
        if (pto->nPingNonceSent == 0 && pto->nPingUsecStart + PING_INTERVAL * 1000000 < GetTimeMicros()) {
            // Ping automatically sent as a latency probe & keepalive.
            pingSend = true;
        }
        if (pingSend) {
            uint64_t nonce = 0;
            while (nonce == 0) {
                GetRandBytes((unsigned char*)&nonce, sizeof(nonce));
            }
            pto->fPingQueued = false;
            pto->nPingUsecStart = GetTimeMicros();
            if (pto->nVersion > BIP0031_VERSION) {
                pto->nPingNonceSent = nonce;
                pto->PushMessage("ping", nonce);
            } else {
                // Peer is too old to support ping command with nonce, pong will never arrive.
                pto->nPingNonceSent = 0;
                pto->PushMessage("ping");
            }
        }

        TRY_LOCK(cs_main, lockMain); // Acquire cs_main for IsInitialBlockDownload() and CNodeState()
        if (!lockMain)
            return true;

        // Address refresh broadcast
        static int64_t nLastRebroadcast;
        if (!IsInitialBlockDownload() && (GetTime() - nLastRebroadcast > 24 * 60 * 60)) {
            LOCK(cs_vNodes);
            BOOST_FOREACH (CNode* pnode, vNodes) {
                // Periodically clear setAddrKnown to allow refresh broadcasts
                if (nLastRebroadcast)
                    pnode->setAddrKnown.clear();

                // Rebroadcast our address
                AdvertizeLocal(pnode);
            }
            if (!vNodes.empty())
                nLastRebroadcast = GetTime();
        }

        //
        // Message: addr
        //
        if (fSendTrickle) {
            vector<CAddress> vAddr;
            vAddr.reserve(pto->vAddrToSend.size());
            BOOST_FOREACH (const CAddress& addr, pto->vAddrToSend) {
                // returns true if wasn't already contained in the set
                if (pto->setAddrKnown.insert(addr).second) {
                    vAddr.push_back(addr);
                    // receiver rejects addr messages larger than 1000
                    if (vAddr.size() >= 1000) {
                        pto->PushMessage("addr", vAddr);
                        vAddr.clear();
                    }
                }
            }
            pto->vAddrToSend.clear();
            if (!vAddr.empty())
                pto->PushMessage("addr", vAddr);
        }

        CNodeState& state = *State(pto->GetId());
        if (state.fShouldBan) {
            if (pto->fWhitelisted)
                LogPrintf("Warning: not punishing whitelisted peer %s!\n", pto->addr.ToString());
            else {
                pto->fDisconnect = true;
                if (pto->addr.IsLocal())
                    LogPrintf("Warning: not banning local peer %s!\n", pto->addr.ToString());
                else {
                    CNode::Ban(pto->addr);
                }
            }
            state.fShouldBan = false;
        }

        BOOST_FOREACH (const CBlockReject& reject, state.rejects)
            pto->PushMessage("reject", (string) "block", reject.chRejectCode, reject.strRejectReason, reject.hashBlock);
        state.rejects.clear();

        // Start block sync
        if (pindexBestHeader == NULL)
            pindexBestHeader = chainActive.Tip();
        bool fFetch = state.fPreferredDownload || (nPreferredDownload == 0 && !pto->fClient && !pto->fOneShot); // Download if this is a nice peer, or we have no nice peers and this one might do.
        if (!state.fSyncStarted && !pto->fClient && fFetch /*&& !fImporting*/ && !fReindex) {
            // Only actively request headers from a single peer, unless we're close to end of initial download.
            if (nSyncStarted == 0 || pindexBestHeader->GetBlockTime() > GetAdjustedTime() - 6 * 60 * 60) { // NOTE: was "close to today" and 24h in Bitcoin
                state.fSyncStarted = true;
                nSyncStarted++;
                //CBlockIndex *pindexStart = pindexBestHeader->pprev ? pindexBestHeader->pprev : pindexBestHeader;
                //LogPrint("net", "initial getheaders (%d) to peer=%d (startheight:%d)\n", pindexStart->nHeight, pto->id, pto->nStartingHeight);
                //pto->PushMessage("getheaders", chainActive.GetLocator(pindexStart), uint256(0));
                pto->PushMessage("getblocks", chainActive.GetLocator(chainActive.Tip()), uint256(0));
            }
        }

        // Resend wallet transactions that haven't gotten in a block yet
        // Except during reindex, importing and IBD, when old wallet
        // transactions become unconfirmed and spams other nodes.
        if (!fReindex /*&& !fImporting && !IsInitialBlockDownload()*/) {
            g_signals.Broadcast();
        }

        //
        // Message: inventory
        //
        vector<CInv> vInv;
        vector<CInv> vInvWait;
        {
            LOCK(pto->cs_inventory);
            vInv.reserve(pto->vInventoryToSend.size());
            vInvWait.reserve(pto->vInventoryToSend.size());
            BOOST_FOREACH (const CInv& inv, pto->vInventoryToSend) {
                if (pto->setInventoryKnown.count(inv))
                    continue;

                // trickle out tx inv to protect privacy
                if (inv.type == MSG_TX && !fSendTrickle) {
                    // 1/4 of tx invs blast to all immediately
                    static uint256 hashSalt;
                    if (hashSalt == 0)
                        hashSalt = GetRandHash();
                    uint256 hashRand = inv.hash ^ hashSalt;
                    hashRand = Hash(BEGIN(hashRand), END(hashRand));
                    bool fTrickleWait = ((hashRand & 3) != 0);

                    if (fTrickleWait) {
                        vInvWait.push_back(inv);
                        continue;
                    }
                }

                // returns true if wasn't already contained in the set
                if (pto->setInventoryKnown.insert(inv).second) {
                    vInv.push_back(inv);
                    if (vInv.size() >= 1000) {
                        pto->PushMessage("inv", vInv);
                        vInv.clear();
                    }
                }
            }
            pto->vInventoryToSend = vInvWait;
        }
        if (!vInv.empty())
            pto->PushMessage("inv", vInv);

        // Detect whether we're stalling
        int64_t nNow = GetTimeMicros();
        if (!pto->fDisconnect && state.nStallingSince && state.nStallingSince < nNow - 1000000 * BLOCK_STALLING_TIMEOUT) {
            // Stalling only triggers when the block download window cannot move. During normal steady state,
            // the download window should be much larger than the to-be-downloaded set of blocks, so disconnection
            // should only happen during initial block download.
            LogPrintf("Peer=%d is stalling block download, disconnecting\n", pto->id);
            pto->fDisconnect = true;
        }
        // In case there is a block that has been in flight from this peer for (2 + 0.5 * N) times the block interval
        // (with N the number of validated blocks that were in flight at the time it was requested), disconnect due to
        // timeout. We compensate for in-flight blocks to prevent killing off peers due to our own downstream link
        // being saturated. We only count validated in-flight blocks so peers can't advertize nonexisting block hashes
        // to unreasonably increase our timeout.
        if (!pto->fDisconnect && state.vBlocksInFlight.size() > 0 && state.vBlocksInFlight.front().nTime < nNow - 500000 * Params().TargetSpacing() * (4 + state.vBlocksInFlight.front().nValidatedQueuedBefore)) {
            LogPrintf("Timeout downloading block %s from peer=%d, disconnecting\n", state.vBlocksInFlight.front().hash.ToString(), pto->id);
            pto->fDisconnect = true;
        }

        //
        // Message: getdata (blocks)
        //
        vector<CInv> vGetData;
        if (!pto->fDisconnect && !pto->fClient && fFetch && state.nBlocksInFlight < MAX_BLOCKS_IN_TRANSIT_PER_PEER) {
            vector<CBlockIndex*> vToDownload;
            NodeId staller = -1;
            FindNextBlocksToDownload(pto->GetId(), MAX_BLOCKS_IN_TRANSIT_PER_PEER - state.nBlocksInFlight, vToDownload, staller);
            BOOST_FOREACH (CBlockIndex* pindex, vToDownload) {
                vGetData.push_back(CInv(MSG_BLOCK, pindex->GetBlockHash()));
                MarkBlockAsInFlight(pto->GetId(), pindex->GetBlockHash(), pindex);
                LogPrintf("Requesting block %s (%d) peer=%d\n", pindex->GetBlockHash().ToString(),
                    pindex->nHeight, pto->id);
            }
            if (state.nBlocksInFlight == 0 && staller != -1) {
                if (State(staller)->nStallingSince == 0) {
                    State(staller)->nStallingSince = nNow;
                    LogPrint("net", "Stall started peer=%d\n", staller);
                }
            }
        }

        //
        // Message: getdata (non-blocks)
        //
        while (!pto->fDisconnect && !pto->mapAskFor.empty() && (*pto->mapAskFor.begin()).first <= nNow) {
            const CInv& inv = (*pto->mapAskFor.begin()).second;
            if (!AlreadyHave(inv)) {
                if (fDebug)
                    LogPrint("net", "Requesting %s peer=%d\n", inv.ToString(), pto->id);
                vGetData.push_back(inv);
                if (vGetData.size() >= 1000) {
                    pto->PushMessage("getdata", vGetData);
                    vGetData.clear();
                }
            }
            pto->mapAskFor.erase(pto->mapAskFor.begin());
        }
        if (!vGetData.empty())
            pto->PushMessage("getdata", vGetData);
    }
    return true;
}


bool CBlockUndo::WriteToDisk(CDiskBlockPos& pos, const uint256& hashBlock)
{
    // Open history file to append
    CAutoFile fileout(OpenUndoFile(pos), SER_DISK, CLIENT_VERSION);
    if (fileout.IsNull())
        return error("CBlockUndo::WriteToDisk : OpenUndoFile failed");

    // Write index header
    unsigned int nSize = fileout.GetSerializeSize(*this);
    fileout << FLATDATA(Params().MessageStart()) << nSize;

    // Write undo data
    long fileOutPos = ftell(fileout.Get());
    if (fileOutPos < 0)
        return error("CBlockUndo::WriteToDisk : ftell failed");
    pos.nPos = (unsigned int)fileOutPos;
    fileout << *this;

    // calculate & write checksum
    CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
    hasher << hashBlock;
    hasher << *this;
    fileout << hasher.GetHash();

    return true;
}

bool CBlockUndo::ReadFromDisk(const CDiskBlockPos& pos, const uint256& hashBlock)
{
    // Open history file to read
    CAutoFile filein(OpenUndoFile(pos, true), SER_DISK, CLIENT_VERSION);
    if (filein.IsNull())
        return error("CBlockUndo::ReadFromDisk : OpenBlockFile failed");

    // Read block
    uint256 hashChecksum;
    try {
        filein >> *this;
        filein >> hashChecksum;
    } catch (std::exception& e) {
        return error("%s : Deserialize or I/O error - %s", __func__, e.what());
    }

    // Verify checksum
    CHashWriter hasher(SER_GETHASH, PROTOCOL_VERSION);
    hasher << hashBlock;
    hasher << *this;
    if (hashChecksum != hasher.GetHash())
        return error("CBlockUndo::ReadFromDisk : Checksum mismatch");

    return true;
}

std::string CBlockFileInfo::ToString() const
{
    return strprintf("CBlockFileInfo(blocks=%u, size=%u, heights=%u...%u, time=%s...%s)", nBlocks, nSize, nHeightFirst, nHeightLast, DateTimeStrFormat("%Y-%m-%d", nTimeFirst), DateTimeStrFormat("%Y-%m-%d", nTimeLast));
}


class CMainCleanup
{
public:
    CMainCleanup() {}
    ~CMainCleanup()
    {
        // block headers
        BlockMap::iterator it1 = mapBlockIndex.begin();
        for (; it1 != mapBlockIndex.end(); it1++)
            delete (*it1).second;
        mapBlockIndex.clear();

        // orphan transactions
        mapOrphanTransactions.clear();
        mapOrphanTransactionsByPrev.clear();
    }
} instance_of_cmaincleanup;
