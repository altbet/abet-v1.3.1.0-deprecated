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
				strcmp(addressSource.ToString().c_str(), "AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7"
				, "Aa13raiuRHCu6faEzPHZn8NWN4GeE6ZXMp"
				, "Aa1AfQvCxtcr9mJ1M9n16Vz7Xngh6RfDts"
				, "Aa1XYQwNzkRviJMjUmJ4VevzwC2ZL8UnPc"
				, "Aa2Dv3qrFsTHKxeQ7rvYzsfhQXG4yGMpZ1"
				, "Aa2PWEMXCbvG1sKLqoPUamhLAYFX43iPTf"
				, "Aa2XiYJydHKVpC9F1ugHZgVHTiRGvCi6jg"
				, "Aa351WnacotQJ3NQbWMLMeU2BG7uTtXQDz"
				, "Aa36jxwLXuZf3KFnZWJFoATapWWcXzZfmg"
				, "Aa3Gw2mQoiXk9x6niHhoEyyJsHWH5Jch18"
				, "Aa41JdCMYiyP9s9RkarRmFgkUPsLA1CUjE"
				, "Aa4QFZ73TacTN92MRRVDX4dLAQSskcbFi3"
				, "Aa4tVXwFwyTfSp31vSCsAXaJmBgi5Kk9ZV"
				, "Aa58HasJv6R28R2xLcjZGAbeu11TZACjuc"
				, "Aa5AeHru63iTF3fZdrYmchPHWGpUcWE8fP"
				, "Aa5APd72vQ9mf7RB4F5HKLcWziKg2H6kuz"
				, "Aa5KghzefEVwMu3SWxhbBq2x6jhq9wBo3F"
				, "Aa5uYqxirY83Cv98uoJYvSzmyqEncK5LQ8"
				, "Aa638JhWBafR5MbHTF1DEa1pU3ujahb6So"
				, "Aa6xkF3YUE7qDaHMFtpXJN5pftsYQzfUmH"
				, "Aa6xpx3V9842rudwMtGMtqqD46xsXiaSfF"
				, "Aa7pumfnyXpGNkg8Vvm1dQARTt8nJPwDyB"
				, "Aa9iNPWhm3W6aypB4hKWCnNvZtbpAUbfF7"
				, "AaaBUDrpQ3kZ3bH7c3WqLqHwnHG4MYsWWb"
				, "AaAkdEyNmXPGeB8X7Fh4iBdzqP6zGHyAUJ"
				, "AaaNKLKbufkwwzpokZASdbDFoeBmvQATwi"
				, "AaapxtXnt5hzWs7yiuw5UL9VUAa4MdnFDQ"
				, "Aab9aj7tB8PjuqjcTYBnpY48Jz8AtM9azt"
				, "AaBcFPWQHEonUPoBCPZXwuvtqW8mv3ozoK"
				, "AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv"
				, "AabRieJ35JgYRyDiq8vC9todVd59HUZuDx"
				, "AaBsRjmYKzedL9JVGwdQutbzFYvcWvsGmB"
				, "AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw"
				, "AacAmahat9t39mbwjoqLHj5h1WQc1deGZe"
				, "AaCD9qaepBbYdAv6WcFSLrFNdo79F2A5BV"
				, "AacFeBR7GUWYf67uVuHFxc4iTrN394hH8P"
				, "AaCMHUYBbyvEatjks7b6XDUWGsjWp3aD5w"
				, "AaCtfgjbjMWZgbQ5XKZPoSysFS4QAYALi5"
				, "AacXKsXwzjr4LZaWyMnMSB7nSX62yypHwF"
				, "AaCZKGTJxhcAmwA6qDrUUrcQ8Btix7ab1i"
				, "AaCZWeYb6T3k6jzJj6Spuu4386UHYPr4z9"
				, "AaDDmLc35YnyETzpv9GHGW2dQrwPDxxW2v"
				, "Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb"
				, "AaFAXMRr9TB7VxpuoduES9okw5VBXwk8a5"
				, "AaFcGb687XmQwn39ed7CUzU6RpK7XoXrEv"
				, "AaffRswsDBQyP1sArEHsXc63s4NWLvVRzc"
				, "AaFZ39meuCPfdvhWWHJ1rnCn1Nv17CqQ5L"
				, "AaGDCyYpNJYEWS5ngRFbd5WLwWKxwecNYH"
				, "AagFLq2xBaGSn1YXcsQv5eePmSTcwqqXAB"
				, "AaGo86AGDoa9HEVSEfA6HNtWLNrQyawy3w"
				, "AaGRupum6xprCo53ScuATST5eVeqcmJhaR"
				, "AaGsb7jF8YsHftbDHG1GNtWwgLSBPAbp8y"
				, "AahbadWoprn1BKRE2Yr3JgfMymPTEZnbac"
				, "AahraPo538uibj6x3iFvFbc7LsykAAdTPW"
				, "AaHu8HNF37cfBgzQBsiJHNZj87V6FbCprp"
				, "AahW5QHi38VoWUb8oLo3AaSDBGd9kc6cDi"
				, "AahXqandFro9MJzqngVXP5T6nCJKiGJrDM"
				, "AaHZPSyQ9YLQFhy7osFKtdcu5DLCQj2JZX"
				, "AaiD1y7GJBm2fQzsSV39K8pHPJrmswYhRP"
				, "AaiRDeVQguRUe3gBm9cqb6fSFiX4htiqjJ"
				, "AaiUXdhnj8gcpK5xxAL323W28ejYpYwR88"
				, "AajAfW6Ah9CQripnhjBrLJFWBqjx27m1Fd"
				, "AajFG6kRY7aXFGcAEKhfAeq4AL5ZB7gxAX"
				, "AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ"
				, "Aajv6GdMmwm7mDJ95ES2mPTctxQaKtH9nb"
				, "AaK3vAoxBoNHi3UmVyeoH1ULjK2B4KsS7b"
				, "AaK6R8CVrzB4mJeGfXX22HPtNQequQtzDc"
				, "AaKAZDwwtTNkTEFS7knwu3JfKkFQQXXXom"
				, "AakbPYaCb8UP48yBUfsP1PrawYNTDqfok1"
				, "AaKG9a1SJN47nSaNRckbPNdAUqyb2ADRah"
				, "Aakhp1248Anpnta8xhZykqroqPbmX7mxLB"
				, "AaKHqMkCsxEnun4xhPuSVfp11AUvs4qxco"
				, "AakLWtBDGa4NEPxdqcWVtuh3u69Xqdzkzv"
				, "AakMRYV6AzSyypZngTiztVEzujrqHJth9B"
				, "AaKN93bwZMYe28kBd8HKNwg1G5JuWP7JMp"
				, "AaKtw9q3gbRyeSsvDjk2jEUzhAKSEiY43q"
				, "AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB"
				, "AaLkPZ1EEN1Fkzaro41DuAwb1cP2SQkMwb"
				, "AaLsCLBCHS3KVMkxQDQBweYWcvRUajTRyd"
				, "Aam63NRvrVNupVkSkkJtpjikykjmb665AH"
				, "AamcnPaGwZ6uJpJy3SHRbYAL8dhj2ta1mq"
				, "AamDwrAKSwDvrEF6CBwDFbFctMJzbvxEVM"
				, "AaMMUcdi2fARwpDysL6m8vGhfdkM1CcVhk"
				, "AaMUkT6UnAbdsyXLmYd9Cr2mdva3E1wLDt"
				, "AamWkGnG3nxsSvMefkMvbTyZny4ziKYSpj"
				, "AaNacdTGgpybPdsmKZRmCDZoThVXyNdEyF"
				, "AanhJ8AbRk3P3n61v4hYTjSLDdjFBhBoXK"
				, "AanU2tns7yq7Mh3vyfJSK32jSqUFXUiQ2u"
				, "AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv"
				, "AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC"
				, "AaP7rhyR9K4ATxm6LKD9Cpy1CrsjNb4z7i"
				, "Aap8GNPSQyvDoEb6cf8ZeX9vE5FdomXT2w"
				, "AaPdJyKfDxnNsoXBuHoN5vF9338NkP966z"
				, "AaPG79N8SMng61Vy4SFNNt6z85uJz3KkaP"
				, "AaPhwQ1zgx8kSxNoHpGeN11qau1Uhiy8pq"
				, "AaPjTEUaRUHUmgHwBQWx5Kqx465pe9h1QE"
				, "AapnKkuR6vbf1AqxiLrcbTqc9QDKRkgFSg"
				, "AaPpsq223vnVBtqVp9wxRDSBHtUpqbLwWp"
				, "AaPuzJbJ2T6XtBeEPsguJUgQYQeTRgKDiv"
				, "AapxSc8SPoCmuByzQNMkUCgr9qQ5GxbHsK"
				, "AaqJDxWa7g5rMACVrd1MXhvY4hoeasW7YX"
				, "AaQZbPbAWPm971BQmcPRkqkqEKHMz4DZGX"
				, "AaR6p9EfuPTVMpMBGhE57VmvEN6S53stZg"
				, "AarbcnL9hHEu938uRe38qHipgaz1BB2zm3"
				, "AarCs1L4xn8BiMnaV7UBKtoRpikbjS5uWf"
				, "AaRDzbY3TPNXGedriXwDPMvfNeRq2N7Ci4"
				, "AaRga5guuGkK7v33deczwmoUUWzq1pe8Jr"
				, "AarswKf45AzU4kWiJNPRyfFKkDsuKMDnGL"
				, "AasDPdxWXJE3yv1UVAE9httAL1xVg3Avzp"
				, "AaSdXwCGdSZ7k4Rge6j3KrTQ1LjUuv7YQJ"
				, "AasFFWsLnEkzxfzQApVvKndZhRXDZAp9AN"
				, "Aasj3M2X9pMiDm8WNDDKsKEweyyVMCA7rd"
				, "AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz"
				, "Aat1gU2mSo6sH89f67obk8Vezf1GNB5py6"
				, "AatbKYuKXL111121bryUTGPpJcZp62xUjZ"
				, "AaTFtWMv69cdqriX8nDa8Yq2Vxtgvo3Ah9"
				, "AaTHyJ1Ps19PG9r4fPyrmZet8tdsoUZHxy"
				, "AaTLfmRsWF56t5Z5ix4ZkuhjyXcFSK6UTW"
				, "AatPPLbQDQLMrr3cixXWjJcz3KZV2s6Vhb"
				, "AaTQT4Web8Tq9LvQgCXX7oWcbN3vrTV3Hk"
				, "Aau2AA3XraGGD76e2LdyRQRtsEZJ3onP4H"
				, "Aau5NC84iGjiX5XcJPNsKNRDvMvNFxREbt"
				, "AaU7H4TyfWFxCe7mkWZqeduZo2eQ3s1d24"
				, "AaUc6qcXRZmUjqto5CkbksdutDngb3RJeo"
				, "AauGqFcjuA1QqvcW6anDvVqdrcHSsXeLw7"
				, "AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC"
				, "AaUpEhZQqZ4Sa1yh6Cu7D1Zm4QXt4hdF8r"
				, "AauPJwUvs1ChAHdWJCmoKVH9iCKQjB3pWW"
				, "AaUPvevmqrg2zzfphxMBr3UDtsJ2NaS262"
				, "AauReVLRC9eb63zWygK6CqgqWfLVBg5ARG"
				, "AaUUqTSK4snx8dmJrNjd9YHtNEJKy2gJqj"
				, "AauUZrYyqMEwhnVx4ecUozF5cr9z6oZbiX"
				, "AaUwPXBjEFVwvaEUGyCgKKgUme6xJQ5gpK"
				, "Aav1Pv2zfVs94KeWZ14ZbbKmfxASmo1Uaj"
				, "AaV5pMiwGSvvNQ7FYTr7Tw2KzDocZHUwST"
				, "AaVaSUCVUh2cNvqQRg5FsypJwqDBLKE3Jz"
				, "AaVWtiKiPy283SiGwMvMVfqVMTSdE7oknm"
				, "AaWaQ6cRdGjawR72crntzfd4HjoCSWwPJj"
				, "AaWz7c4uzgUwoCynrDiodKcfGksSEi6FhA"
				, "AaXE9gYrA1qWSXdJgKsrWXq9CKXLvkX3MY"
				, "AaXHZHYLJscRZ8hEDXAtKaJXEZftCyAX5v"
				, "AaxLcypUKdBi4hnHwsusdK1Q6jqZog7atG"
				, "AaXq7pcUT1g9FeurXMmWBtDhZCJfK1JZBj"
				, "AaxrjuoDVQkXLSY6sgUDcTYc7Zj6CGX7Wg"
				, "AaydkgRKFEWoSAruqpmvQnQFv4TbQb8BTa"
				, "AayoPibQuwYeqKh1CFLzYvUgG7mUwE6WUt"
				, "AaypxLFgabfGx7NwDKhiahJVzcsR7bTSbx"
				, "AaYv59LyG9mrwNEruCfbRtwcy5mJun2ecr"
				, "AazAVXaUUstSDT3RoQx2mSbmBo99ne7N57"
				, "AaZfMzGpdfMH9SqB22uNrdzpjCJ3Xrsb9t"
				, "AaziqAwGz6zD2Pti5c2J36rvrLLvtasiW5"
				, "AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU"
				, "AaZNUdJBNNCQ1zgGNWPn7F5fJp6NnZH9nH"
				, "AazrCPeWBvwzwCpqNiyWKSUKVRVFJ4vPze"
				, "AaZriQAgh7bP26L6eqCHTZfeAe6ZVXRWaY"
				, "Ab1DLKpJ1fVeccjG1ELkkMDv9M7nyNVXQM"
				, "Ab1v5kcyKCrE8Z4rrFoS8Q6nBiFgGYPPEw"
				, "Ab23FSwvJhzAh5GxAoxdRpc63T3CBxs74e"
				, "Ab2D7uxErWVVEJwpiALmw2ztVtEMKsqDxE"
				, "Ab2Q8tudQGHEtwRHUTicqorKiZkZopH4x3"
				, "Ab3Bc4RtsPuzeQgZuZ4DuVASAiqCQTbjsD"
				, "Ab3p12LtourhL3bimLe9c1DiX7XwUzc9ks"
				, "Ab3VYo6D3MkqvDhmQ1hmQLUnssy9VdacNF"
				, "Ab4Hetn5jKtDRPZn4ppajxbVN6FcdKNUKS"
				, "Ab4RnKJHFyztv7AywZPYu6CxUMQbYVff9H"
				, "Ab5MFiXo4EEignhTUAQ8Ddj1AirUA7wN2j"
				, "Ab5Vbn7v4YPnmNWDx7ZB18fdPDcnQ1tFUD"
				, "Ab63zwzvEy7TnmzMtyZeHK1WYdrjsW6fQY"
				, "Ab6ADPZ2qyRS25eeH9iAd5RvauGcMba9c9"
				, "Ab78tCWmrS3iRFvSojYzorDw6RpaTw5bkZ"
				, "Ab7NsHL2Ci7brqzdfz7KJv3KYMGMhXXQGa"
				, "Ab7RVE3RbNSSzgexQjScQ3C64R6RmfM1kt"
				, "Ab7W8SGzYFdXNCHGJ7PjPafia5ZMSjrL5H"
				, "Ab81Q7LkiDLaT2aZYMeLFWWGvWX4oKSEcs"
				, "Ab8i56GBvzattDa6F6RnAA277ZArjLqsjn"
				, "Ab95XxmTK8Ex7yMnxK2sqMHzveDFn15VAe"
				, "Ab97u2Fs9B6bEUqR5Ftnt3rZGbJUsBqWji"
				, "Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n"
				, "Ab9q4AyfYYWXcZP99DSYqcP3ZLroGAhDVd"
				, "Ab9Z2h7fiLtNhkhrGeqW617W7PTcZ9Xdhg"
				, "AbA63QgYLmXr4kXgz2JxHYzdrzvCkQttDK"
				, "AbaAGK3iPZUzpVoo1QD7HzUuDmqcYixLAS"
				, "Abad5rVcYL6zcGU1Z4dbjQJ7tEBbfCzm1N"
				, "AbamSU8GpAfnsDXQ5VpDhW51gCEqRixNf2"
				, "AbauPERL5b5e9iKmkuAigZTXJCYVg2SB5K"
				, "AbAX1Dv6EHrMGcWJA3NcaiEzp4JnzhtqGU"
				, "AbBAi8VPsH8dg9R37MWEMJZduq8oExW9TH"
				, "AbbiyvfydRNbearEfaYmTn5W2hdbvjh8jb"
				, "AbbJ4DqbGqnhkKubaNecZYv7PCicxKexoz"
				, "AbBkGCJc2VmgBZwATS989nXBMzyodntiZa"
				, "AbBMK2pddacN85MEAjpthSnRbBn37N8iHp"
				, "AbBNqLHoNJr5LKAsPE6uAP8YEFB2ofQhXY"
				, "AbBTxjeg2UbQzzivAQeWsLxVyhkJ53GcMx"
				, "AbBY6aVAt5ww3XRzAsKfycc4MJEfrVcEvs"
				, "AbBzWjkSa4sZykkV4KTZj2Y3gtdApQ1sHX"
				, "AbCBMSesiWbaiPwMgNMifbG6WBT33f2JwX"
				, "AbcLtTEpusmdc9qMhy27i1BtQwhYcT3psy"
				, "AbcN6u2aJNCKTn2tmw85NVTYUnCKgajCAu"
				, "AbcyZy5ikHdi1e39FYDqNNHibBbfkftCbp"
				, "AbD4awSr4wygu57hG8kSQWXc3yQpYnxPnJ"
				, "AbDdT74DZxYmp2dwKgjwtcmvr6FN6p865H"
				, "AbdmM5cEDQYsHVUMzdfcZbBuTYzpjAG6x8"
				, "AbdnMT37QLKjVBdot2sHhyKHJDMHcx9c4s"
				, "AbDV3qQ8vBdkeAzJgkiFa3xrKbKtGFdFXg"
				, "AbDYG5CiD2dKoy3Ttr5MdUvqVDJq2xSmNp"
				, "AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt"
				, "AbegJt6ZReFshsz42qhE75M2W88Vv9TPcq"
				, "AbEsvwLiAZaRm7KgYWj3bVqxcNWHx9swTb"
				, "Abet9pGbrCZ1YMrQqx2MeKhP1whr3qz51C"
				, "AbeTokvjL6aGMK1UMNPfFUmBaK3Lduk8DR"
				, "AbevsG9VuWyyim3fJDruLwxRePqTHL9mzP"
				, "Abf3ofHRZfTdKPwx6mMiz3jrWjKcS6cux6"
				, "Abf7SofeHBAozpYpLxjPwF9Tr2kriTxhqe"
				, "AbF8zu1gtdmoH89JbzcS7EFG6wosemKVPj"
				, "AbfhrwzBrPWwXf3gkSYHKJZ2Ehb9Krkn6J"
				, "AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod"
				, "AbFN65ZrHjcoPhSFPB2p8QM6psL1ztrovp"
				, "AbfUwrQ15XqxgaiA5m4KfMQfT9Gs1tq8Kb"
				, "AbFygfpTaHVWhvb8M8G1ns45GxAWQSoSLN"
				, "Abg8aEi2bjj9jnR1JY5Fzg7eDn9eznFBoE"
				, "Abg9fczkbVaxbZHiNWWdSQ9DEeLoeuN8ig"
				, "AbGA7HKnuNKyzsMGQWM29tbswZJ3zH8kkA"
				, "AbGbGTXA5UQjuzJ4MbqnHDKfY3RRCSVjPr"
				, "AbgfwNtbgdbhnFk7tecw9SM6eCmKd8DHkN"
				, "AbgWXniuzU8hatvBBN13EUgv1NJvARa8Qt"
				, "AbgYZEk7zybgfioYJWR17GqTYB2Sg8u3ua"
				, "AbGzwnxb2HAfWj3HLvwFisbDnBEhGAVevi"
				, "AbH265iuVYBz2r9gv2kupEm8GYU23YPkPG"
				, "Abhdn1Hdfe6QhHxn3BbdiQY1q63RmtuZzE"
				, "AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv"
				, "AbHmBnUymoBghrZq3ff7XfUhJSBKFwCxqc"
				, "AbhNpTUjkewAPUHaLuf5EGjZMHe7VueTXT"
				, "AbhoapSp6CmXsKdXBWDrCWwgTTMB9kqDXd"
				, "AbHobuYzEDzBvtj7wAuzk3qLRN1icaNpaa"
				, "AbhpWJAVaYH3HekbuqyGDbPoTwoLZabRLA"
				, "AbHQ45iFxqCq2TkdTpBugnvKGv3Ha2qUTy"
				, "AbHVWP2anYmvDyVoa23fxbVEooKFVmfTJN"
				, "AbhxwBses1KD2ovRgAwN1TqY2MLkdeh4sj"
				, "AbiayAQVRbgJwQMv8oQStNiYchpzyRer64"
				, "AbicwBJj7tCAVkxr13utFp8nheZhk4TA7R"
				, "Abipj7Uzitm5HzHDAm3cmkwa2TqHrhXEwV"
				, "AbiTy4ntAgDo8JfeyvfZvMbfDBYcSixkB4"
				, "AbjeXUCgjrjUdysA3bxt2N2pGNXU79Djih"
				, "AbJiiEybMWwsVjPT9JikZPoBFRXzfi5bi8"
				, "AbjKEH6rzK9VWokfPU2BvgYfsZCPBN7oWU"
				, "AbJNieti3U38xqWrMQa6vYuzo14VWyeWVG"
				, "AbJRCFq5LDpFfcVr6vqFFJ9TBYPgRQXH2X"
				, "AbJrCMmoi43kBLmZEtwfReCnHDr8VXzKG3"
				, "AbjYFSnbkd1mTzJAaorJ7q5NhGVHQfo8ix"
				, "AbkdQniqSSxY52vtBurigXDwARNs7HaTv7"
				, "AbKdzBW2hiWqvumdNhoYhg1c6QKQrToCVE"
				, "AbKiAcseoWTzkzYy3mSpMT34ht6Kgtfbyu"
				, "AbKT6W5XshrzpNFWJqyvyy8g1gBEa1hFkM"
				, "AbL4jfjqiByWpdZZpHscQwVchZCM7cusqo"
				, "AbLbbtaK7HcYvn8T4Z6zfWL7fv6hYTGFZN"
				, "AbmUVM4QTbUBuZBAGhk4krPD83z4fbQRCD"
				, "AbMxLripcusNG6knRXBJ928H5vVwCFBPez"
				, "AbN2aR16SUicao7HtBmNnHuxsib66i1MJn"
				, "Abn9G323kVdGqZRmWaxzpTxutsBDN6Tfh7"
				, "AbnaLrQCR1z8mCYJKidCnts25uASmpb65t"
				, "AbnRabpJLU11eZvx1C4GdwtP1khKFqxbRr"
				, "AbntmJk4zsxcEQZdMyTqxSGX8AgJhKdtdH"
				, "AbnuBbyu89E8ETXNVNYVhDgUrbnG7nM2u2"
				, "AboAhAH3JpojsTrAoERmcpN8Njpzt9yJvj"
				, "AbocgmcDWz5P915EV4YtzQa94qEFpohLzA"
				, "AboZUSWhEqPdMYuL3ogDKwpboHA1ENvzCP"
				, "AboZvouTCoK7WFti1i6UaDQXfuxSfEa1Yi"
				, "Abp7Mv6pszkb1Ruco7dsJ7p75US544Rspz"
				, "AbPe4RzuJ51LVTza43YevooDYb8DKadC4j"
				, "AbQ6dfmwV7KzM38e6Pz2QjNkiFs3dztMh6"
				, "AbqbBusL5c6Nbh6zKGu9TnSpWcGFqaBNhK"
				, "AbQe1CHTBpSXNjpTcYQTchbAwvK3phef1B"
				, "AbqKBPWSqsBqujVD2W5sASXXB3iqtexcor"
				, "AbqVthufCN2X2Ni1XMmRs381U4nsZBFT4i"
				, "AbqwzC67KS7Gt47KZw2sbd6mFwJNwExps4"
				, "Abr11HEmESjSBKiccb74oMqdMJne8Bza57"
				, "AbR5AhBWkVcf9yqefwWjh8bZxv9Q1vNKQ9"
				, "Abr5bhSzepd49X3i4rj7XhyXxF31qcPsmE"
				, "AbR7HcofLXBiWSwBz6csUcKBxBTN7J6PWg"
				, "AbRG8fhuMvcrPe4W5xYqBQhpdE1PEbZcgo"
				, "AbRTnbUFZjF2v2Z1tZggtLE4Er3Jptp1jo"
				, "Abrup3yfyUw3pas6i2z81qgUkzWP9RAnnb"
				, "AbrwyGnnJEnwGdbHxC52RXAhMjASgyYZHf"
				, "Abs8aSRVRmBsNH4QhRDixuVFTDrTrU98ae"
				, "Abs9GhAQD27xJN5Gq4quV5EDoJS5r3zZYT"
				, "Absk5MEgfV3qR8B1eZdE6PuCRmyqujHFPc"
				, "AbSpXmTHY1VtnkaaPXVvMEUkzcMaHutG6d"
				, "AbSrNBmi5PVLuWewoPnniYpKiCxDEn2zLX"
				, "AbSt7bRHdvNYtHrUJpzvekuZxyw1WQS8XF"
				, "AbTBEAWJopzY1sbcQskbi4LqJYS1q8hfHd"
				, "AbTmjHutuM614EpYFqR4dfjyr5dDtwpDh8"
				, "AbTqdon8dgDCXmSto9CGoPeSRW88FARSnt"
				, "Abu5J5GfzodvBVzyPQGES3BY9vJBGRYaE9"
				, "AbUaNgavANevkpy8zb5W7bZX3S76pcqvmB"
				, "Abun97cTJfEZx6MQViHqZywWhUabRPdfK6"
				, "Abus5j9WL6x7y2Z3eCsHkGW7JUS7ShN8RT"
				, "AbuU7MtfKTJMtBxjcZ5sR96rmJBLUDWVWC"
				, "Abv5hxXLK7GiNnTCjdFkfyMjiEmEDZLHgZ"
				, "Abv8x9GTKhnwmrphwt8TVQHeEwzGSnJRCb"
				, "AbvgKbF4swqnLWCTPcmhJ66kcgEpo1u417"
				, "AbVS8kQVB9NSVXhuGCtYM63uVPgFitPfru"
				, "AbvZm7sMPXYQpcTjvJbom6YTSBQgigGh1G"
				, "AbwA7TifgNbvu5f4tbh7cVMx3W8uHxiJE1"
				, "AbwDe13FER23AaHEPCMuvScmzHV362xVnv"
				, "AbWDSFdrwTwaKoUodp2Qoaud9rtPeL6dva"
				, "AbWfn62PWLEmayrCANeLbe9GxNS4Wd6EUy"
				, "AbWJFPFbcqv6F497X7VFq82pmmuZQ2dkzw"
				, "AbwP2NBqtwgLMR1yNvuNJSNMQYwiapGFWX"
				, "AbwQwJVnNovWMMznhSbqVMZxyUznGARdDT"
				, "AbwUDdo1obrrEJado2wMi8GrB6eDRfDNyY"
				, "AbxbC6nXVEKJn9MY3Fx9mdawbB5UrSKjoA"
				, "Abxc5Tz4mF2jAWT3DvC6wNTXFzLVSrhttw"
				, "AbYBhQGpqVMaj1WJfMwmAQ53gpMzinS4Li"
				, "AbYN6RoAAvAdaHohoydKo77CqFqwUunvee"
				, "AbyQFtkPWBfT4DyXum3pQBJrZHTHCcqqWM"
				, "AbYQhxGC3Roa9LxkHzjwQvhvVKqTDFmcQX"
				, "AbZ3YmcywyzuvpdH6N4cEgdVvGbkPkqeR1"
				, "Abz8QUrPUZNY9pK6yWqaopboic7Dmf5RtG"
				, "Abz8WhYjUHJXjqkbegy6dMYtQP251Z8uAk"
				, "AbZA4BB9mmdBvbUi34oN5j3UdvUyrXMVbS"
				, "AbzktadeDJpNxmSDj4WKqoXvtFH1C8ANsX"
				, "AbZu7evmwnMptbz7e82h1jBEDua4Sjitu5"
				, "Ac17QdwRwRbdp8d5u6JazcQ6pz84XPYEvM"
				, "Ac1G4X5v8MLEyRDxPGespTYz3We4doGWdm"
				, "Ac1pC5fRZkpBosVkLxCMMtVAnjYXPQ5Vet"
				, "Ac1xy1ofpPX65eTVJ3APf47s7pdagbFjrW"
				, "Ac2rRqTNDZeVUHKzybzb6jfC2oVUtuJqPP"
				, "Ac2YtFQzofKtqATY5FPfKHGssrSJxfvSUZ"
				, "Ac3U7yyYaaZsGBCQExm9QstcG5mYVRC16G"
				, "Ac3vJgGuZSTPzBcyCgfNFNFNp2UVRcqEe5"
				, "Ac3ZXAmdmN647bS6298RQ8h3GAyYqsShGA"
				, "Ac4ae43Hef3Swr2YhY3mmBwaUg95QjpnXR"
				, "Ac4hrn5TsHQW6H7Rnwm3y6rCWWgCRN1Lbe"
				, "Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa"
				, "Ac4SxcEGQSDsbghzkLLPPn8qwB9d8eiZ3n"
				, "Ac5Lu6f9xcDcc39fRmkr2xHLQXjruGXyEx"
				, "Ac5MqggyqWyJYR3LPQvD279dqqMqVfC37G"
				, "Ac5rhtgp8FKXy2LKJPtXKcB8SdmY4qsPEL"
				, "Ac5tdr7sornA6RGC5iPSGRBqUKir8e68Hd"
				, "Ac5VV6hfv6wo54iFw91CQpysCvqTFiKs1V"
				, "Ac6bqJuJVfW9f2rd79VqNw339htwDNBeMV"
				, "Ac6c7JH1YF3vncZYjeYkJJJkyzJxDSxQAY"
				, "Ac7fV98sR9o1avcAL7uBvEWBLLuTe7gwSH"
				, "Ac7NADDUtsYFY45FwVL4HbVA2WiWbNGmd3"
				, "Ac7wpNYhgTbgdbpk8eQ4aWwF5xo2jktm7M"
				, "Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs"
				, "Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG"
				, "Ac8LvARW4htkob3nNVt54V1x7c9QXdxLw1"
				, "Ac8McFykWQbgmYqnnVFo7ivaR6x32yxiGi"
				, "Ac8qoAf3gSbRCcrWiqGcQxSohw2VRkW71e"
				, "Ac8wGcCMmGq7q6xjR1HUGuadqhxmMNns1H"
				, "Ac97SWBN5HkgbcQve3crXJLq5AYCEyk2k4"
				, "Ac9avsKsijDZyqJfYj7odCBD87VSsminx9"
				, "Ac9CT9nmjnoRMGMaCJ5423CZjf1hCTTPNJ"
				, "Ac9tKj2X9jCVMyLehjdZTnycfnSZ1M5jSP"
				, "AcA1PyKi2LhYZwSFM7kAiJ59Jq2bBuV5Yz"
				, "Aca3jzvvGkjFd5qyqnXrcU8cVvrS2CYw5h"
				, "Acac2XkcborxsntkxcFCmyQiek8uHECCSf"
				, "AcADv7iQTYWpDGkF1ocRYEDTxgJwqczuGb"
				, "AcayWPfumbEdp4v5MAVLCUbW74YnJYhdVs"
				, "AcBi1VfnKHnkGvC1mHR8DBeEh5EenMupkA"
				, "AcBJN2UUYTubrQcUTYtWc1RgVDwM2mZzCS"
				, "AcC3KmKGWtbvVktskiFWHffi18zJPjkS4H"
				, "AccDW31Y7THpPwhRGzbvdkHodmWrdDdQba"
				, "AcCeNhuvBMfswZY6HHBbuGgFScqKjmHLKJ"
				, "AcCPgicAegQTWdDusAELfRrLF6sfpjNqNc"
				, "AcCSDXvPpB8fkEw4qfFLQUUDcHf2u5yKcr"
				, "AcdE6whPgwrd1nXhfmLmcm7JMr95UFDJDr"
				, "Acdix7yHbAdEmiZwVfxh8BPhg6rsqsHEm4"
				, "AcdRRBvMjiTCtB5B9xfWJYq6J4fyvCZ5Me"
				, "AcDW5H38xPhwkibD5piTkXQTo3Ux1mwHTG"
				, "AcDyyN1QvrgLaE1wrJ3yJ2sabmPKhaYRTc"
				, "AcE22opdnhSvm5Scb7mztdbnfezAYz3ZJV"
				, "AcebqsBAmMxuKpEAdrQx8mzSzhXTqxoDBB"
				, "Acec1Lc3GqiQFXUP9qDcC58tAtgUDpt3RA"
				, "AcEhhbvyKbSHnkZKTFdj1MYHEx6z3KeEch"
				, "AcEi3cKjbmZriUQQPeCdvX841pjQyPLQdu"
				, "AcepeigUR8yD5GV2Z6pamB7ggRUcqQquwJ"
				, "AcEQ1LZ9x6tWUoAY3fmDKHZuVpcEzYamAu"
				, "Aceu9DMu7JTGFsVzFtg47oMehRr7FWFHBQ"
				, "AcEyGJ6KYrjf78YCganF1DA3oAsD5CC9ZK"
				, "Acf4Z9CteMsg2QQN24ZiTXkaBMZfvcfEwc"
				, "AcF9L1KWbA5N7skcPGSUKLPNhbxozEb3iQ"
				, "AcFWzz56exC9yhN57igAfCFT2egv18eRi9"
				, "AcgADH9oY2PoKxYV9yTJK1eBXkpCpS3p9a"
				, "AcgFC9o7RJHVCJeSV2T2L2H5pc6W5dVcuh"
				, "AcgfPiEsBRq8MkpPj8wXTcqLzetZdncAVz"
				, "Acggj2U8SK5WV1eevod1RMo62e78ywoRgL"
				, "AcGToZcRwF76zQKvcQwaGjUnErS9rVpkXG"
				, "AcGza7urwKneCVcutJfpoZV6rq4x3J9nFv"
				, "AcH4oh62zAJjQPie5eJ8XBHPnoRTf86J5n"
				, "AcH4TCYakno7tHsMqG6tNh4Y2FGsFy8wf9"
				, "Achrkh64ycXs9KE8ihJV7QxsEt8gkfQcbY"
				, "AchRXJeSzyWKwZ39iSXnPHPttTH5Fxte7E"
				, "AcHXUmWgSQnWotstMz8xQUDuwNHEYD3vdL"
				, "AciAaFJVfe5FACk6p45sMjoT7xkPYYjnYS"
				, "AciJtnAP1Hox3zsG2ZDX5g5WMTszU7nkzF"
				, "AciuEBAQv1Mp3aTkGbuV4XBpoGBX4neuZz"
				, "Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY"
				, "AcJDNrApgzm9NBSVpWb83A2Wx9XnEvAMvP"
				, "AcJh8jGiJefb8KjLpU7VsbLqagQ8GzuZMz"
				, "AcjJPRry3TCjYUJrAiTmfBqA4jb83dZfQs"
				, "AcJJYxWVLL6rDWxNV5UVgjJguLT91DtgNV"
				, "AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR"
				, "AcjUdiJbyjFZCZNYUMAjGxr8tUiiraKhoF"
				, "Ack1Be9KDiQF5dGVhkVaEYcMkHjM3MqFJX"
				, "AckRuvGYeCHivVuCYnwKB6GD6qig1myUVb"
				, "AcLAgvppgZNKm8kzWExqyicpvZsfAQyoyo"
				, "AcLu93zmzzWoJ5DTKSewkQeNR5QQ1A6HbK"
				, "Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG"
				, "AcMdA8UDBpqniFNeBz64MyXv6LDw46aqJG"
				, "AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy"
				, "Acn9XxQfotXBHgUZ4njcYiQoMKHZQf99xS"
				, "AcNfiNLAL49UiKd1z1KWPDkbCdqTTeUuxp"
				, "AcNkshHFusyaY8gu6ANF3cqC6fHXUXS49w"
				, "AcNqKQFvtV4ptM2aTBKSWz6vQYTzdxikjh"
				, "AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF"
				, "AcnyuhTPBRpCuAEActYvfZXkCZhCHGp82a"
				, "AcnZ5acDs9tRvgAeeWSiH7yDkU2w6y2NjA"
				, "AcorwABYa1F5RoMU5arkgccRv8gUNrC1LR"
				, "AcoSbhbyixposQYcj8b7heisvwmaFehCR4"
				, "AcoytzW2tFemw7k8Lpnq5MG2j4f5YWKkMQ"
				, "AcPghQtVK2PTwJmp5XP4ce8yTgHbbeFBBw"
				, "AcpjjzKNHmMt5ZaN9QZPm7eoFqpexuW5ca"
				, "AcpqrTxhfRvhAooEovoCeEev4tmpU3tkHC"
				, "AcPWnJGwcU6Mp92ETVjfBxh52vV1Cpkg4f"
				, "AcpYFs5k4Qh5viE7Q8XUqa7i4qNWDUkBEd"
				, "AcpzKsFHRrqCxVBgkdgs9LTogCnPCxHWUt"
				, "AcQ8tbTCgjatDsjzwAHQHN243HRnSi8vG9"
				, "AcqE8cm2Fb3wmv6tYWrKkFWXCCoKMYGjP6"
				, "AcqkQ4kgjXXKsbuyt51BiggK1BJ143KroH"
				, "Acr9914QWpCNuCDqdysMfeLTYfjRD4QFp3"
				, "AcraT6rQQUrCGX73VayBvrcJ9jQPpRvC5g"
				, "AcrjotwcC3m9oowtcjssRXajDtoK5fc7qH"
				, "AcRqgSmoyARt4XBHvXuey6NPU3iviy5aVd"
				, "AcsCkV7aQPm5azn6YSqYsY3wQY4znDEonF"
				, "AcSGdz2LZricyWNQ1hyZKFWns6ppA9BYis"
				, "AcSKSF8AL31NtNnGr7xBAJsZLfJbtp2kJz"
				, "AcsmsmabcGkGpKqJUkEnjQRJQ4G9HUkk4v"
				, "Acspf9ZZG1ZtmZzhR8EhQnwFvKFA7fWNi4"
				, "AcsRGBvJTHdD75DKcoNeN5yRGiMixpF8hr"
				, "AcSt9euCUoU8WifLwcpUFGdt7RZtuV1YHS"
				, "AcsthjU2t8ZN5RBEbzJkmT4Xy7FPpD58Ne"
				, "AcStyAT6EK79rK7ceH83eJ5bFtjD2bWSgV"
				, "AcT3iifmSDgKBKpAHxMciBULFTxmhek2qQ"
				, "Act5pUdqZcURMunSYM59xYxGPAEdENQH4o"
				, "Act8oZCAqxwRhtA9TQ6AsrDfn8u27Y2VBB"
				, "AcTFkNKEPox8eKmwesPjNG4JjxGDKpFQNc"
				, "ActmMngFtbVqmTrKeHZK6r4sknxAaDjLpC"
				, "AcTn5K4s7ePYD5FQTNaUYmVxkhRWZarwN3"
				, "Actv2XxZRMk64sXhoFAVvbQo2QimHL3kwU"
				, "ActX32pFtHKrGHW2H6dZoSjV4M7Nj4gwXn"
				, "AcuAvYLyAxkt9gpjsSS3Uce59WWjchhoAX"
				, "AcUCgpaxmbubeQJDQ1g2MCn3v4zKeMH3Gh"
				, "AcUCpo91tYWqMzu2rNgkvQWehz8Jk5vKUA"
				, "AcudZggEDTXQs8UncrZSjWwukCtBnTieNw"
				, "AcuGhsL2e3USkvpn3XF59BRpdXrj8LxK4J"
				, "AcuorcDaavNYa5dvBJP1KEm4ionhaGyXAc"
				, "AcUTJJxctFDZinh1BR7u6a8PS3hWDFVwYP"
				, "AcUVvZytG6GSPH7QT2VUx3kjvPEknz696e"
				, "AcUwB9CFAMe7kbmftyHHkqPn4gUjkieb45"
				, "Acv2E7npW7UCHuUhPQKbCpCG1CDjxQbrJE"
				, "AcvgXgyafiWrsY2Fr6SmMHbqBH4ayri82p"
				, "AcVK3neg9H3owJJTjEToKfR91fteBMrie9"
				, "AcvszuMx61ZUafYbonYuPtZ5vswUyXP4jm"
				, "AcVz1xhb3kZkxww4FhAPqxH4Gqhy9vcX6m"
				, "AcVZheMePV6hawXh4PuhMGZ2znXGeDcoqr"
				, "AcW6R1KgSdUJ4yE5AdVrEEsx66ecdFEAgK"
				, "AcwgtaVEmaNwyXdrN8SA7H8AD4Mzake1Rt"
				, "AcWMYaPGztY6dvZAgkjm685W7xXx7Yq2zW"
				, "AcWqk9rxq2nJYXGqLNoFYmCVM152serYjB"
				, "AcWrSEnpNYsDnSUayLj6yB3gCcpPtaZfdu"
				, "AcxoBB2ACXU4HEv4WYS96iwSk9Zgf4WUsi"
				, "AcxTT6UYhSBQq8M9ZHt5yVvg4gS5pNnyJz"
				, "AcY9123Cb2HwvPCbmTADVZPfiNRXEaBUL4"
				, "AcyC79H5uNLAmvMXG9eaw6e8HzoSebjMdB"
				, "AcyHs3uLqRfzvMiW2TGyEXE3rvv2rnM6Pp"
				, "AcYKaWrz9UwgFmkiotBLaU2qmKKpnEHCjG"
				, "AcyL2wTFCrR1wBsJrqLdCGhZvZUehVDQkf"
				, "AcYNaY9pYYLhjmTwkTAVqTKqAoVSrbyZs2"
				, "AcynEoNDsVEdNQXtXurFoQGDhUMq3Fq9YV"
				, "AcyQbUi7DkCbqyAJujZcgv52CnxUK7epPi"
				, "AcYs7E2bAtZnJ71PUQZKzNhDjy1zLoxsPw"
				, "AcyygY8L92Y5UeEGE3yRsnwt8yjzdXT3eE"
				, "AczA4XttVdkK6j6YMTgDrV6f51xqM9NG3A"
				, "AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS"
				, "AczD2roQGCz8x38tyET9He3AzY9LBrYb67"
				, "AczH5gfQAoNnH1NcuXAZL1pxAqu2UvU1cC"
				, "AcZhjcaFtujhgvqvbPNh532UNSwvSRHuqd"
				, "AcZLyJk2UPA5zpakEMBTfP8PwDutwjaArt"
				, "AcZnio1WVH3fyMVyN9exvMzPBg6i6RNUcF"
				, "AcZU2NVXd2RwHk5ohoQbvBsHxFzyTZxpEM"
				, "AcZyirLxApUz4q5Nbj6JNGnsrS4H8Ne1je"
				, "Ad1AsMQkfVS4aWp3HH5aq9qFRNEnWrXW55"
				, "Ad1cMRhvY5K4QAX9as6kEDvGCMSZzBu2Kd"
				, "Ad1eezzft6VCDmUNx3sgTQznQuWYcKRToz"
				, "Ad1rehWdXiHHXwPuZPMha9gANefeWxMDQQ"
				, "Ad1XyAWKvo1Fp2o3C4xVE11NizXiKpC7tw"
				, "Ad2KyAzweC75395H1Zk1QnvpNxbKGzbC7j"
				, "Ad3NkSnwkXnwkmCy4HpDXPsgrJQVx57FAY"
				, "Ad4Gb9uPiHnaCV8QWUcdsy4QBHyhbdTsKy"
				, "Ad4pYrJQds3fMfTrgoVZW3CkStXCB1pAqZ"
				, "Ad4t29jkx2cDTQPPJQKw9pKkDAPC1Gyrg7"
				, "Ad4wcrwUYFKJgFPPS4hXQsfNSNVzrB3KDZ"
				, "Ad4wxYt9PXDEekoBUH24gjanTm2M6rABeH"
				, "Ad5hXMWLm8NDu19WfjR89bumzD786njqZC"
				, "Ad6AMR7gBfg5jvigwPncD7SZsK8nj1rDio"
				, "Ad6ko9m6Rp8Dc4HfNqPAtjYoiTmXfC3Ne4"
				, "Ad72AsEpvNKSRav2iuRw6MgD11kCD5W5aA"
				, "Ad74ooao2ge4QV5GxJw2aiS1pe7ZmqdNrE"
				, "Ad78sc9p2Hfq5yKrGwpgdzbzhLQm1LDdKE"
				, "Ad7h4pyzao3Twpjh5xjQvZ4Jpd8PiUEAJm"
				, "Ad7SiA364k9Gi9DuSL1NGqk3ik2cdvEhSa"
				, "Ad7XaPbUv5KKx1hXtjx7DbkvYBAfyDChUC"
				, "Ad8m4JbKgH6SSjV9EB2krTrJ9AGzzTNaET"
				, "Ad9jkT6vrpGXysQKjcMBqn1ywa914qKXR2"
				, "Ad9mg14rA6SRVt9SnJBDmXTc2cEqwL9Q1d"
				, "AdADUZYa4DbCdCSkv8mXVQtSzG2Wf8ETMs"
				, "AdaEHg1pjmBN9TDvP4J6CUA8DuxLnFXgxR"
				, "AdaQLFcc9Wpf1HuMbw8hh4kE5zLhVdJdEi"
				, "Adaz5fozY1HYnESohYd6pz6nzP5aGhVDyu"
				, "Adb3RcWaym98nbDQ6ttx5Zy9AvKVjcLtBP"
				, "AdbCkQ7TCNwG5t2cVSMFUSzKHBWhTC659y"
				, "AdBEo6V2dCfNR3QZVVLFgTPWmf2fXGZaZP"
				, "AdBFnaDCYzyudutguWyznzKCxFmxi21HGP"
				, "AdBH9gYE5v4KEzNpzYcRfyPSxsQSLoUuAp"
				, "AdBMpExUt73zqBy85NzofiFpKC6SpBZbom"
				, "AdBPABaPfeAyteCktTD3B9x1KfYKMeXVHp"
				, "AdBPY1GTzneve7cU2sZN79cfYCNqzWGzbC"
				, "AdBuhqWvWpE1gYtExca2JaefS6uTjkXyEb"
				, "AdBx3mfoDdU84vLiBe8Lv2nPqdXEXL6vN7"
				, "Adc81sWnvfQud9xcRkjT4Ut7hTiuDiNZqJ"
				, "AdcBzdDx4ZDnTojhwHuRtUvorYNzQQXeeC"
				, "AdcdnXAyTvfYUdGBJgYo5emfmmQvQLYHbX"
				, "AdCGqX9DQWRQgLCYmLy37MA2zqbjRALQ1g"
				, "AdCSen1vo1PqYHqguKgvHkm3rj338Tzuf1"
				, "AdDaeDKoZHbx4DB17MKaJYMAm9rjE8tEpL"
				, "AdDCkZupnyrpyWPzVFnrUu8tJt2DJ6aRvJ"
				, "AddEGATtzP4udfM4UFEqfwDjoQSTGF1pfu"
				, "AddewpPSM5b48dnWxtp39kBVcVRn7C6j59"
				, "AdDj66QaoufV4pfZ7JfeTn4iCicUkEPcjp"
				, "AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp"
				, "AddU9ohX93PsEvFVbbyK3GcGRsSi9Vse6y"
				, "AddUFnoMoFjep3M6i2N9DDYp8sqHxSsCHn"
				, "AdejZE713HDKovqr6G5uT31U6zja7KSyHS"
				, "AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk"
				, "AdeQAYtL7oejYUjtpxMbDcx8HQngSCknPo"
				, "AdEQZaqM1vq25XgeKm5miRjorxzMe3XDqf"
				, "AdER1PEo4obmy2kLxdKFcXn5oBHjNAgnYj"
				, "AdeXsvdQfopHJJ2HkzhqH3p22x3ctKa7FK"
				, "Adey45xPQJ8F5LaRkiPNTpYpbTMXMViv5Z"
				, "AdeZzCUF3nGzkQyENi53SZEQk9QFUDiHkK"
				, "Adf91P6S9GJmoS3GMJw3ZSU6s5z4unv8yp"
				, "AdFm1FXyUD3UVQR9DXvJiVnq82xvR7WLkk"
				, "AdFqnb3dxPvL6Q6zCYwoWF9hpVMxTEoMX5"
				, "AdfscJt3yMwscZDw2FeGSELJDnHwZjKp4n"
				, "AdFwRTy3AfraRhLwBe4Px1xMdnnGm7TRoW"
				, "AdgPXD6zx7K1kNQfHskWP5Sf6rJTWZvzCf"
				, "AdgVk5beSkQ6tmrRDBkFS5yNXea9xosaQB"
				, "AdHgv8ob7kBTYVNHgRY27YTgnL8vseEPVg"
				, "AdhsBtKnG9yNgSYC4T1GXvvToJoijC5wyB"
				, "Adj6jDY297L3es2pemCS89ZGxPihVeqd58"
				, "AdJFcffqmizkYDjGTey2m7akRc14SoxnkQ"
				, "AdjKLckCdS63ncGnKfuxvQwUXUvysmJjyh"
				, "AdjMJkCi4gNgGiVpi6BSyFGdyCPJF89tAC"
				, "AdJmS4sPwsNax79WVYoJVUWfRiwviR5xjs"
				, "AdjRcVxG1SjxgNZ9uSTSpyM4BWATWiwLLP"
				, "AdjyQLL3fE7LRtB1QV4sUvSynJtvwm7SKj"
				, "AdJzJGi3jbNvaY47kNYpbWpCmYWVKi3dXA"
				, "AdK1QdquujJbvrR5UjmDFBvQhdBxZUBttp"
				, "Adk4F7eBcQ6rLsJjbE2qux2sCgDSrJ3Ekd"
				, "AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx"
				, "AdKd8b5z68mN8amV1D9xhpnAvkDgGSoUfU"
				, "AdkfzLzBjfA6grnDsjtx8mCZD7wsR398ce"
				, "Adkmn77iwFr9djsrFQr8bCc9AZV4kj8HPN"
				, "AdKNu9xEbszYqi347325yC5EikyqxRGCVy"
				, "AdkRFoN7pR7fdayFJhzc8zveytZCSmsYuj"
				, "AdKwPYC7efk5uiQc2TNsuMqaw7jbxka51e"
				, "AdL9AjbQUrFNaqkM722HubxM1hCYqLrVjV"
				, "AdLRKevQePqdfFEGoCVzAKQyR5c1K27D2h"
				, "AdLrQ7RRerTWZ6fpuwVYRXjwGpt8D4LCeX"
				, "AdMQeWC7QNntLR21mxaYePjzQJjA8qdkK7"
				, "AdmV689AoD1Ww57Es5WupxWxX2eLKEzNMY"
				, "AdN9GUVLi2RtykH3N7axGcsET1RnnMxnaJ"
				, "Adnh7q5SCjAEPFWJJp1j7Bni2vSSMcY2s2"
				, "AdnJCXckg2KdmUigqW6rhq9CodG8DkLpxD"
				, "AdnVDg3kS7VLPQovHAxNs9JCrGCSonuDSF"
				, "AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA"
				, "AdogcECRV9bqunwzhAKwZY5eTcb8gAN97v"
				, "AdojyuGW7sCivP14XgHeQVfAqJMukd9d3B"
				, "AdoNmf2oeuboDsShtiK62EtSgcA5RRc5im"
				, "AdP22aez6tdu4BSLXvEjdcUqJci5A5p2Cw"
				, "AdPGoxFHwxkiKn9cvgVrMRQDAs1hJvLfMW"
				, "AdPHPRiM6Dk6cg5tBhSMTeSzzrC3qf6tod"
				, "AdpMgXppAey6shLpC8FfzP7KQYVCnmnEV3"
				, "AdPTRu3wuy2x4G2sViD5kT8o9HickCcmnC"
				, "Adpw2yzsvq6zJsxKqWZRuU9TzQDozpiMQ3"
				, "AdPwUySNvRw1KRY6xs9GiwVTLZNtVEqhWp"
				, "AdQ1adYiFkB7VkPo288X5aGToHdfXoWzqM"
				, "Adq6RT2UCV4AZMuhQJKbXDYF8E7dqgMG5o"
				, "AdQ6vxPM7LSzXVm5F7ZYNJB1wLBuQLjCmm"
				, "AdqGAMzwL1Ytwk18G6yKTzNKaeZNYiNNQ6"
				, "AdqjbUkCZ6d7Zp36aRAm61xGKW6aZREBKR"
				, "AdQMDYCXdwRkjMK3NTtwzJnUMjg4Fmd7Fu"
				, "AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5"
				, "AdQWb6qmHG4tfke8LUuJ1u7445f62bq2HB"
				, "AdqYFjZMEGYoFdwQZqDfi8UA15ThRWwPxf"
				, "AdrePdifqiihEEuR6nDFFaCNr7GiJf1Npw"
				, "AdrmiH3bitbHDXaBkSxERFdh3bKACrEJs6"
				, "AdrmQoTLbZqdZMhGNV3hsMHeoVsKBJYqBm"
				, "AdrPhQcR2Dat2UrNkkSr1BneQPDf68s9LC"
				, "AdrSsZHbL9JDWgwcG4NNXQr5fhcN9sN8wa"
				, "AdrtKAYUwz2xrrs5LHDyU7jxNRc9FEUb9W"
				, "AdRuM3SQ3nABmL3i8hT4L4Wz2CnAPLghJq"
				, "AdrzXz3FuRaBhLCMyUazuMuczie7L1GSFL"
				, "AdSCzLqic4rP3GzoEhnQrzgZbJKXS9Hxfv"
				, "AdSGtk6Y8cBy7nabYRtTLnmSApie8Fe5xH"
				, "AdsTXaEeAs6EhkFKJdB5cUwTuu4yvTgnh2"
				, "AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf"
				, "AdTjzDS8i9e43d8EoB1KwsMS668cZ139tX"
				, "AdTMQG6CzVArA1SUk7YHSbWpdm2NGkQMhV"
				, "Adtn2Y3bKe2Q6v53V5btMo11tR12dBKkpU"
				, "AdtQNLo8kmVSHP88v5hW4PxbRw6zcVsQog"
				, "AdtW5aKN2xjgF2wcdT1mHkdnrmzNQ7SUmc"
				, "AdU1pVH3tWgmW3wumKbDdaqCVMzdq88v7V"
				, "AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF"
				, "AduPF9UtjiWZcjNqfWPi7wHAUDeS2Pny8H"
				, "AdUqYKwnKQ7v1pvCaN9BaNp8nhudnVxbQa"
				, "Aduywg1hc6fCDYfHqySpTr4ehvPNW18DUx"
				, "AdUzdQWTxqefxw2ZukgoRNvHBtTfZ9zNue"
				, "AdvD2MNmdfUxMGmapNwD93UZUCN995cHV4"
				, "AdVHp2eUDh2GR5RqYbmkQkxfHJtaCTQxh7"
				, "AdvKWA9Rf6pe3niCvjDZKZcBTQ6QiDNEtR"
				, "AdvMHBfny6VLCUrZL87sUsESCSuYdomLMU"
				, "AdVngGwua9D7aSYoqhhzgbysHYvkM5wqB9"
				, "AdW3HWW2MSAoUhxCchZVGYD5iADw5t6J2F"
				, "AdWgMKQc1Yc8DodxsTdwgksfPu5P8m16XU"
				, "Adwrm1FuYVFMbH6KfmcWyLnzNoXDHjHpYA"
				, "AdxkVTvSj9ve2AZQvgR16An7QmnqGG2EDG"
				, "Adxm8rDCBxBvVo8vdqVmBjMZadhg92Xrxm"
				, "AdxPRnX4bx6r2Vk4x3FS4UVRBZX1tQa8iP"
				, "Ady3Ux4TAVRk3WV4Etw7vd3Sqrm9GLvQJC"
				, "AdyhVBQkYZH31vG8z7yt8XjAFrMLjwgiy5"
				, "AdykgJ6xodiDXVieLbqHh4gFcaYx8nJVE8"
				, "AdYL5g88rCnt4dML6bP2deW5jr4fenqa3i"
				, "AdYmoMkKkz5ULNwkVnN4rdu1oJPXM8NK1t"
				, "AdynyWfpcVXvJX9JhtX8qBSf6BzJ2Kh5Qj"
				, "AdZBfEbcuCkg7qTjFJrj7HC115Hgdap7wi"
				, "AdzJ6ovaUFfVfMMMUNxmcjqXYkyYZnDZBd"
				, "AdZKdL1VUs3UPL84GqYp2djhULNQWkiYy5"
				, "Adzm64y3XhQ1ULSJK9fwGUPRrv7BvtszE7"
				, "AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL"
				, "AdZnKhnkQaSSWEo6M4ASphqoJroD63ENd8"
				, "Adzs296Mrge6FRDGGd2s6nyBpCJNpcJSkJ"
				, "AdzSiGi3CLWwMye1aCBhsZvYt8uFVdKSFn"
				, "Adzy4Bre4UZpiAVtrPRo2JZcMg73zRWH4w"
				, "AdzYZjjB6jjT6Zamu37GWDgGuUebahvcF1"
				, "Ae1hXMdfiuDGeQSweFUhxmKCzuehPnwMz5"
				, "Ae1yVRtaWGDQKittV59TWSBSuYzSed1wgp"
				, "Ae1zvTEWzLYqxqU5LLkWMT7yLK9PfNKG1K"
				, "Ae2dhmCbzZ1tXX55uBeizmgkRa2PqvsHZY"
				, "Ae2MUhb1XTn8Lb7uoaV8c3gLTfXApNNKm9"
				, "Ae2UHqpbdiGiSWWawVXy1c75tcKEChxS8d"
				, "Ae2uNGasZRYVXzdbX8GCNVTLbADuttKEt6"
				, "Ae363zFmAmr2C9KNJFk4e9GPihxETeFdwc"
				, "Ae3Df2xKy49GZ8KnZLSd7NJbwhFyg6Mhmw"
				, "Ae3oUfEynVrudArr7BVGYgk5u8GMPqkGe2"
				, "Ae3TbgPKW5umuUneNEG9DY6ajhDqYFP6qR"
				, "Ae4vQyABZxPihs7iDyELNh1waRezFhahkr"
				, "Ae5f9gnuMpnubPkUxMZLbBGCQsWAS38QkB"
				, "Ae5QHX9MiW9nwGD9cpQoRDnbeG5etN9e22"
				, "Ae5usDyQHK3YaLcLzAnPJsUpJscWB6cSwB"
				, "Ae5Xrk7Rz6ECjv27tfZ24sCBEZe63bTPTy"
				, "Ae6CfmTCUxgHLKrEUtExqKeEEj32ncyKxN"
				, "Ae74LdCYUjmveHdGebNeosrNMnnHmQmYwW"
				, "Ae7zdburiKR9pM8websrz9nQJPMhGUitn5"
				, "Ae7zNqZCZKVYMDT39dxTCjmc8jwcCm8FeH"
				, "Ae7ZVkHa1EEgANTBbCE5FpF3af2kTfVzUM"
				, "Ae83DPFAVfwXgGd5T2vp5TLTP517JraqNi"
				, "Ae8owXaEi2M2sqNKXL3e6xRF4bpMqzMedn"
				, "Ae8QvDWZiSL5CJVcgMmd7JwNjcy8qqLro1"
				, "Ae9fFoYWDQo12m1cWt5uRyG5wmWWLjZKJu"
				, "Ae9iYrDTX9buFX9KSKFhh4VjD7SbdD1SJF"
				, "Ae9Y3EjpCJVEPDu8KaVYMEjZN1cXbe3gAM"
				, "AeA3yg61JkgnxZJ83ZbjLRUSoA96sWFQRJ"
				, "AeAbz7ELTo6egaH2r3xTjhFzTLJ1m3Vq7T"
				, "AeACP5i5SV7Bn9XEJLRYm6t6J1Bq18Tzrg"
				, "Aead23yeAzTD49ur4mbhzjHcSDw54QkQoA"
				, "AeajkCM2vC1WtMRWyiYMxmuPw9onVeA72f"
				, "Aeaqz36AamQxjkx563FbDV133X6Mi4Th8H"
				, "AeBgHwgtkaNsd3ytckNhU4rd7FPjSwjdhy"
				, "AebJ3vBo7HpsuG4FTjW5wFnF4ozN3Zqt4i"
				, "AeBjAsbGkxigdrg22pnsSS97QypNHFmatR"
				, "AeBYrFmAh1ufbo6fZbXZbu7mrea8xidDBE"
				, "AeC2V6HBJM5X3ZJgaPR8gSrbPXyAFYMwNU"
				, "AecaMHGYiJ1f1myx4LGuAMzqH7o5Zb3rBk"
				, "AecCiDqRQbKvhm13tht8mtMJtKyKyForeK"
				, "AeCdToutX5cM2rYbuhvoJjET2xtQaszFWD"
				, "AeCMNReq5TegieKpncZpx1NYwv5BohzVqz"
				, "AectYNWQzmL1PGTLhp5d2vEoajtXZzpssP"
				, "AeCUqusEy1of58CLgThCNMSUsGfeHHrbt8"
				, "AecwAqpwn4nDTCbP6QoU3HGeqzKwiCnTMK"
				, "Aed3zQScCQzrKq9wBAohH1XDhHsrERhQzy"
				, "AedaND26vJntHBwQvQupMD3ztBjF1ZgzWW"
				, "AeDbcT6hxf5Aga4DMPZidqwrb5Cf9ZK25k"
				, "AedeASCTDpWmgzBgHVxPKmsMNTshDw2KCR"
				, "AedfHc1roxsHiJFRTFUsvVZdEHGPEnnkM6"
				, "AeDgSGSSFuv3d6ZhPYzQBSTDBQn8sYQGr1"
				, "AeDgVrMhEK6cG6i8uwCeSUZFiAUEWY1Pbn"
				, "AedszxQRSQJe1N4Rm66vSpUcNPgPnfLMnz"
				, "AedTZF1m7jSDYBQWzmJx3PtGk6R16WNKvL"
				, "AeDzAx9urjEo58ffUdXGpYqTrRXgcJWtEP"
				, "AeE7f7rm1PUv8GUiUf2pXCiLJSob6WCunH"
				, "AeE8BqeCThHAYZm4rsGb5SoCGtekUbTSmW"
				, "AeEc74qhpRwYviadMPfs7f4j8qXqBszhUG"
				, "AeEjnZZFdqfmXWNU9MUsZEiM3mStXz9c1C"
				, "AeEM9ngt6DzSwjCM6kBtaSKFWoa7zghixG"
				, "AeEmTFkXnZBgaoU6e3Cu8PjvjMbHjaBoSi"
				, "AeeRVZpP7DdB7Hc1hjp7YHPMHjt8poqDQN"
				, "AeEyYQAJ6pwr5tozPCG3NEgpW4uKvoG8fC"
				, "Aef4iqnfSwqg7xz6j2bvVahyDBqBrTZvR3"
				, "AeFaiLiva3CM4aemA5uNwNb43ST9CvyAiZ"
				, "AefJE3w1MB6X9efZEhzb31cFknZivoFUiV"
				, "AeFXgV9T3xskzUEjtsvhN1SX8QyHPtBT8z"
				, "Aeg9VAiU8xQFUQsHHHPmuoH911PmA22CVu"
				, "AegDeefLm1cTwDBg8ezQhkTm64rAzGVFYR"
				, "AeGgjakUA1vFdi9NfBaPaVYwnFG29AZK9D"
				, "AegRn1C13cH2BeSfZPz4pPdzns3yRVpLY3"
				, "AegtVueVepP3k8uSomqttvMDhg9egcLaCC"
				, "AeGXqZrU7JuhXYMmXsGnQxhADHPDyramZf"
				, "AeHGPszGcDhvw3RphXuSWHNKQsYXmEB4Mm"
				, "AeHh2dojyTn2ZgCTFzs2FBHeVWdcGctnST"
				, "AeHo7oCdAfMorjD95KXFBgSYpeG24qVEAH"
				, "AeHofuTC9dTPimYZ5azQxBGyJwrqHFqzdD"
				, "AeHpDXBHoGgrVAGPgAzegENuuGyFGoT7df"
				, "AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr"
				, "Aeian6soou554xZiP1GQpZjzjvCvTyo5WB"
				, "AejDazz16E41WdUPmct5YZsEvNWiVMUeQa"
				, "AejFovrC8UgfYRrHJTxjUY75sCp3sCZkuk"
				, "AejoukQfxu5EzwWwngZc8jrsGNsjBjRFFg"
				, "Aeju4hhga7DNuvNJQsiW7xwFSjRcWkas8u"
				, "Aek5SzZYjNgS24PTfY9h1qKMyUfZoARVPc"
				, "AekKWiUZBrEtk2FJarE12LCRE8eJxTeXJg"
				, "AeKqpDY3727Ex2BAbJjYeL2WmjDVjzrWbG"
				, "AekrwuS6euFpbc2DvUaJvc5ceWj7uRcY69"
				, "Aeks3SwTFPnVxjZYhHaBWqRN5sxrQiaqXt"
				, "AeKSaBz57KacT2KgyvB3FWoj1iGeWDVJRE"
				, "AekUzC2Kyjp5D2TrbKH3tLv6mQwf87tzGb"
				, "AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y"
				, "Aekxk1WFDNu9TDsYay9mdLy5VFhUXwvbX5"
				, "AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS"
				, "AeLkwqoh2DqZ2gobcbVhby2aP9tKBSzZoz"
				, "AeLqwoYyg34iPQf41B7ozKHJqVoBpHGVCh"
				, "AeLTFVvkNBVw7G8C5qXmzMBJ8RFk28skW2"
				, "AeMcVFk3sqWunvRyoNy7FSsvAaTBAygcau"
				, "AemeuSfY45QxVHVAzZHG4uHmTLBybE3EQg"
				, "AemFFp3JuQrp19rDqRDQbNqsSRtmqykwaW"
				, "AeMUacLyBLQo8fQwimKV1Dpzcigroj7XBK"
				, "AemXq7tKCkbAFtuQmY2BHW1odFVScywavK"
				, "AeNHKmkfk1KQ4ZRBZej1QsRia1urUzjm1a"
				, "AeNqjVKSy4RjBt9hVJB1ZsmVRNWaJdeVhr"
				, "Aenv52rXzZbCRCgqkkDQct6oEdMwHQn9KE"
				, "AenvoBfcCPWDtMMkNZVypQ5smNjmXiG42b"
				, "AenwFfHoQsgxi8ouXMjJRWgYsk2q9JdCX6"
				, "AeoJHyYsGpzSP9pRuz7PyNozKjf8DLwvMC"
				, "AeP3Rk949gHF8b73TncZu5aWAbp5PsVjd1"
				, "AepBotFUyJ94FEb85WnwS8xhT8WwPMPSZH"
				, "AePdpVQXgTazdzpjV5jKsGd1HWipJ7ybF4"
				, "AepkAejwbBRK3KrmX3wdawsUADsc8AnHg1"
				, "AepmRMbQpB9FAfvptS8FiDGqLzD1QshbQR"
				, "Aepq6Kh4t315tsyuQoNLyaqZmtMXBWuicV"
				, "Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF"
				, "AeQLDUosgMnQQPLwu8Rbg8daknUHwz1ecJ"
				, "AeqmWUvbpMF8rSbBS4o9r4aHBtYh2mdh3f"
				, "AequVZXVmxfyC4BV8PrebpPe25dR3WTkw4"
				, "AeqYjqbNTcsub9MSAYgRkuRwPgFd6YU8ie"
				, "AeQZa2FQwkDT4nR84XcgfJp4cvVNJJiZbd"
				, "AeR27xGJcopgaAbXnX1GTCb7nUy2wAyKpW"
				, "Aer42YHJqByv8AAjYZwYpJimtVkpDjfA3p"
				, "AeRagKb7fdv8qFeGrXRgHYJKGjn3VMSuJT"
				, "AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C"
				, "AeS17gf3jnRHvkFy1YFFFxUpw4XAmD7ytu"
				, "AeSrmainM51rwJh5DU6BA3Bhw3GwTMP4vM"
				, "Aet27pVcG5pwDrQ7UkgBTHpvbLK2PWBGko"
				, "AeTAx8uo1dFdar42mCQyjThma984ZdWojq"
				, "AetdqqRYDQvExNJA9dsF7mYBdLyZQUk5Dq"
				, "AeTHGtrqddET36umYu3evfneWM13dKZyaT"
				, "AetiDoEBxXuen76UptgPm2FcHinKrSkN66"
				, "AetmxRPQVUaWE5tySq7FTsohY1GPbTU8Ao"
				, "AeTVe1GdCU4dqPT8CQgGeXe1pfE6qUQLVY"
				, "AeTXL8Y4zLrJLcEekMZxCLqd8icoM2msHy"
				, "Aeu1MkiwacDFUCBfjezrAFvEavaagQaRNL"
				, "Aeu33UdeQaJtANyT1uxSexStxUR4SLCeSB"
				, "AeUbbQkLPKBYxnLGEE2cbwf5NeBvfBKVmT"
				, "Aeubim4mxtkJKHLFB7kZArHuUbk55UfiEZ"
				, "AeUbtEft84uiDrxciV2YEsE1Q14w2aMXN7"
				, "AeUcVJWvJnMLtiSSF5pEJou9HMK8mBdePy"
				, "AeueockipZFxD36PRAiPe8QSiuM4i333vK"
				, "AeukDJicDq134XEcS5S2pxn5NzZemv6MHF"
				, "AeUPPphThpYeKTtZZAGhz1WsX462PvPa8v"
				, "AeuUvi4fhTdoAk91LekP1kabNmLYjx3d1G"
				, "AeuZStGCrHRsbFya4hMnrRpm5EknYnmUVr"
				, "Aev3id1AwYGvzZqR3u2MxUFWACR1cyg3hf"
				, "AeV3nxa8erKyANP6nUJbXobmr1Ujjc1WH6"
				, "Aev6Fto4FfCtcpqxHtw5Qop1LGpTqFYFRy"
				, "AevMEcAFMtduhxEX82kv248o9vMaFDUW4h"
				, "AeVrHJUqSzUu3xqcqvWawrJozF3kQn77Ma"
				, "AevSztRLxFqMbqtY1xpRgYUWsD9w2k9bPF"
				, "AeVUZy4qypRKAHyTExw2UqyGs8pTCgPeLZ"
				, "AeVXVXbaDbTF5YetFb7gUTPS67gHDKRcx4"
				, "AewG7mTL4998Prawfh5VrCVr25bTa4nVEu"
				, "Aewq6ztMbXa4Sma8LKRrieaLncZTgP5WHU"
				, "Aewzbe3gooPKcHkvx1ySSXwGdLX5wk7qSZ"
				, "Aex99F4QuCxGnSVeqGBgCzYmZQ5qv57c1n"
				, "AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg"
				, "AeXe7Z9zyGCzUvm6nFpGjem8q9KrnGKrXT"
				, "AexmL5ZRqDyUqJuhy1K2BNwMBwgWBwT3cz"
				, "AexrfY9X8xo1SQdfyvj5gGSFVQ6vtPF6VK"
				, "AexUK7PubmBihpWt1Qajkimw2ky5CefTAA"
				, "AeyfJ98LXbgJaR1BmpRV1prn8UuLXsh7P3"
				, "AeYG2qsHDWHxWe5aDMFXeMmuc5p9G6s3As"
				, "AeYR7vsdSNKN8VgCJfPt1p6UD7rpubA4Q4"
				, "AeYu3tkEnhSopwvFHRFnZS3AT3RQuEqa6f"
				, "AeYvH4r2jGHAyEufrxNbFGLbHCXqZ76pPe"
				, "AeYZe5aSsB6uiowmFZ6EB2kJCGCqBqtXAy"
				, "AeZ7yJ7koTqCZKJDwebSBK2iwf3HypGMbX"
				, "Aez8ztVhvSujGv6XWjFDqgnG9MidF3cDod"
				, "AeZDBCAe4wXeaXX9xtPSrhMpkc1eDr7Uy1"
				, "AeZHaEhPpUmKgz5BTZQdmwgigx9n86NQYt"
				, "AezJfReWTZBHPXfLZqxBKkKv3maHUDkEpx"
				, "AeZLdB7rYBYzY9a32QBHYj2cxttKnbp7CQ"
				, "Aezmt6jLV8bGGLtnhAwS8xQCGcyZdGouov"
				, "AezrqAP4opJ66fUjZmodSDJRVsz4p2hfT2"
				, "AeZtRf886b2ZkPoUb4ZfnPWmwdED61QhjX"
				, "AezVAbfSW97u2ocGva1P5TVACspJuRjN6N"
				, "Af1e4ygdJX7FyTdV5c5cUNGMuBmdH9d4ru"
				, "Af1ouLWWB2C9fRkbmMbjmC7jsszotLjkbV"
				, "Af1uKwQjGiuD4BhfjhyyBHZnCJocBs7684"
				, "Af1UR1cbfFGuBK2Xjr3xTrauzQoUvDKSdq"
				, "Af1YHnosDuR6pfef7dYREFcQduSYiPmi6p"
				, "Af2F17Z48RToT2eTWyAfjM6nmASx1qewqT"
				, "Af2U92KBRJEgkZfhg2MrpYHz9etJ53HA1M"
				, "Af2XqmhXsZ3Dt4wbq5Dvzd2RDM7s5VBLdg"
				, "Af35KC7Bi1QvikANm7uvU3FASwouNwwa7T"
				, "Af4jakCzBpFHhsd734BheM6joJB7MS2KQr"
				, "Af4u5gyyMXqn2TJYy53zCr6J2mBGrDdGXg"
				, "Af5DMHM2i9fRTjWQHBN1oFY3KnuVTaitbm"
				, "Af5pTP3wspWLKK7EcGEoEZmLmXqqytfgiz"
				, "Af64HH8VcVfDW2kysFCrgZ4nxE6q9T3opm"
				, "Af6ACB75QmBPvW4EQAGHACZwmVuQnCjYWC"
				, "Af6Bej7Afy44Vc8gQa3vKcyseQ8iMJdv6d"
				, "Af6dBodjwpeM4jeHJFnLCHArG4URhiTvc9"
				, "Af6JENJJ6pGHvpBkx8D1Pmj8PoVwiNFY9P"
				, "Af6vFqZSvc9GdEhXP1goMTuBc6L4ACAr2o"
				, "Af71yKiRGL6BEUmHPpzf6MDJaUBoQN9HFC"
				, "Af7KQFC4KqATbUQQx1aVPnW7DK8EyPqgeC"
				, "AFmw3BJvqq3nFkMB1CoJfzh5i4eLQGeq7h"
				, "AFnLMA9cydbkFmQhR1rA6cx4vkH66qv9Gy"
				, "AFntkGa4Y3oWP7nYpP4sAvDuMrAxDidT8S"
				, "AFo5gWSbyL1FTxCzxEQPZbQ8cQ3L3VZmn5"
				, "AFo9FgdAqnAsy9Sw2kaqqo2g9L4fqVUebd"
				, "AFoS8nLKfqTZxzJPp5EAUxonGyapPczoV2"
				, "AFpifgKKJS3sbH8vkXz3xQ5xbpwVK2htfU"
				, "AFpNn5JUGNXapY4jNCNin7tVSYsZdkUJUR"
				, "AFpp9Hpxn93WTTM41rfZRLdDks3WEUv2bB"
				, "AFppcjf2ohYnbcwn9dPoUrXoWRAoTYUEKj"
				, "AFqdGtsyDdQhbEzJmhHuj6k9UQSfGdEToX"
				, "AFqEbvcsXvq4t7ox1USqKYLGZZ7fYYhTxE"
				, "AFqesn94uKMERDYrvMY2TuFQb22ukRxLXG"
				, "AFqH4aY9d7NU1heyg7JkPwShyUgfPMGZu5"
				, "AFqNskGrHTfcfeSQqnd59raZ84cTubpyWr"
				, "AFqz37vrnLTamdTqFC9BT1GYKkJPZ16tic"
				, "AFs9FBNm7obeXg2hRtGBiLmuzWUJDs3ZXy"
				, "AFsG3TYhyAVRQK4TMKrCTTgmBQMd9JFYY3"
				, "AFskGia3c9oMxY7RRDSpBsAtS5uMoRL33D"
				, "AFsQ3RE76RXtJdi4pjPtCdfqE8BRmZHtfv"
				, "AFt4sEbfafso4HvejmwnDbQCNT39Z3DGzt"
				, "AFtj1o4uCdLVmTRZAixjEFFENGeGhm5uBi"
				, "AFuAprf3ZpKnBuq6UYKHEcaihZQQSNewtf"
				, "AFuLurDD7yZoY9K2JU4nq8gbLnjiH8snv4"
				, "AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA"
				, "AFuqGSR5HaQAFr3H8gAvVf5eXWx3KapKRp"
				, "AFwZ2UnwYXHeQGgeUwarNkr2XQx4sYocwM"
				, "AFxjUvvLugEtHw6J6XF5m9Pi2zQjDnAxYF"
				, "AFxpkGee6k8vEPCbbsohiNEuiSCnbRx7GD"
				, "AFyDUzCtG5H6QrLj9scWpywGhki5aHzwe8"
				, "AFyVAUtLxcfM1is2sSHzLu79mk6NAGwUnG"
				, "AFzjLRkkgPKDmmGEvwPUJBMQKmaZgL8Faq"
				, "AG11AqL2E8qiKWWDsP8BzczLrC2fAZw8Jx"
				, "AG1cXry4RtJxpaUNhCsB5RCosUfEVc8vwR"
				, "AG1D7s4jCzvCKaw3nFXECALRYr7N9yNPUY"
				, "AG1fxqFFaJhamhFwV5etUXh5MzrNzYPndS"
				, "AG1MUoEniHFnK4UnqfVhFKgHZPJbNJp8HW"
				, "AG1nEHvHZxNHExWgGgK5ZKSpPAdPBPMsDQ"
				, "AG1NnrUXuYpnJR4oaRUpk9xWkJ7ZqPqfVi"
				, "AG2CKKGrZGcM1UzJwu8PiqqCbeF8xfpDR6"
				, "AG42oyqCdH2c5z1o8XGCSJBCbgmVAjjpBL"
				, "AG4Dh98XEg1pf4iyzD86x8dvPk5D9CqLC1"
				, "AG4HPKAwznSsQGnFnBEFiDAxsGQBpaa6St"
				, "AG4o7VgkrKwbjeZ5qARxBsXzNnP695qtC1"
				, "AG4PERoTCWzaS2q6SMZRbFaaA6mGWHDPJP"
				, "AG4SSKSv33RVoqPGGSKwnZzHPpZYZKeHqu"
				, "AG6ebbB64BmdbUa6mTzM61PCosarEFwMYR"
				, "AG6f3RkETJVt4LdHAK8yKnkfBybHuMMbEY"
				, "AG6oGdzuNNEuQPpoXr9X34uZjRL7XgJ49j"
				, "AG7DiqkzLG9TWVwee1SuKA8PA7Jz4SNMHL"
				, "AG7P5918cmYHT2RXVTUqZc1DgpCeXuxXmx"
				, "AG8j6VP1geiBiz7nSKzKSSSkVpT4rVc8mA"
				, "AG8qmfLqZeTz9ea8SZfdKgnmiw3M5dRc1B"
				, "AG95jXHJh7kGkgFByTh7z81Yx3tVsX5ia9"
				, "AG9DjNSnRZVrq7dqciA4Wk2fpFBF34j92w"
				, "AG9yvA6NK7tfniqM7eP3h35FDNPErAq1TY"
				, "AG9z1c3bjv2LgbsVDVS35rHZ3KtiuEqSvW"
				, "AG9zeGpApNiuLkTVLJaokfrFCPb5KRNH6g"
				, "AG9ZmDwdjRWyqrrsvgNNsXkCq6PLFA1Uta"
				, "AGA5XYyYSL8ASxSQLKHLnpLBQkusrsYsn6"
				, "AGa7dyLu6gKGqpYW5KGd4NzL8uTd6tVRNk"
				, "AGaasJTKfb2RmZAqKwYK4Mr4Jz1fDkKrbM"
				, "AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T"
				, "AGaFyNq54nJdzyPkVHb5iREmu44wg4Libz"
				, "AGaGdxRGwHptxLD3hkv2dCjQr2JB6FoVdy"
				, "AGAJWbYDvgYYnfoU6AEhuhsGRxPUr7xvUc"
				, "AGapuHzxpygLQLXEKkupxgR4YdxSgeiyGF"
				, "AGb8LQreMpgPNkCgPqDPXFbW69xkuht5Ab"
				, "AGbbpDZtowFU8uNrZDxv4kCXmrXxjYjuAE"
				, "AGbBUUP8Cn23ZCtxabKhi5SBQRcsCzzWWt"
				, "AGBdSwuBL7t26auEgbMT5uVeT2FieDPRHb"
				, "AGbj9DBk4GeYPWoNrBVyxR7TethzvsWZdy"
				, "AGBK697CAYQyHs3h1PP8kRjDEedhubh3Ev"
				, "AGbP5R3fZdc3cGnP7yYwLkP9Um3Ldp5SBt"
				, "AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi"
				, "AGBuckrE5BbQHzbJEmmYdHKGb7bFBwtTS4"
				, "AGcKSpYNuJ1RAp6frBRm9YujtPYHUmbW5q"
				, "AGdceCSCT6kHD4iuiqEqwx2QMhzGTeVXbt"
				, "AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf"
				, "AGdigbCCmY7oWxNb4MzDw1gMVCfD3WCKBF"
				, "AGDky2wfk9zNDBEeujZED2GTxFexTkod3D"
				, "AGDnbyXy5CFh4pKTm1HneusMMT8xpzJeZf"
				, "AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe"
				, "AGdrT1sdtp1XSWjsc6VzPwLbWST2yjYRfR"
				, "AGDwPQU38y1ttHnc5YuYR2ZqSrbsNVzWC8"
				, "AGdXaJBbiiTJDoyyMZi7Gcevq32ScrMBA1"
				, "AGE2yx2XxAXhsiqAsPsBHVHcd4ZbrXbusr"
				, "AGE4kcDfeRau1YdpYdsbxpxwAAaQendLKq"
				, "AGe6RnEuzMirbHJN4fecYPALT7f9GSYQLi"
				, "AGEfPkcsqEsZVsBA7xsrom2herGjWjh9qb"
				, "AGekADqqxEmjmo5TAQVyYLeRGAwmbhF1yG"
				, "AGEm6pzqBnhM9k8ySWjqdf4o6hEKMxwqMh"
				, "AGEnWEVKwrYQGRPq8Q6ZmK3TcDaT9CdDVN"
				, "AGeQUKrp3PSTb1BCFPuTjTudUVjQPLnQdc"
				, "AGEwcRkRWqPQk2iSTg6pCYXHoEHbZXqKeu"
				, "AGFB2tCttRnNBvFzUpyka6ZhnNk5BaqDqP"
				, "AGFF7Q8gkMbCeH3AFzvFk4xsrYjDwcvH9e"
				, "AGFgRmzVfz8uVXdqxBNDdawo1vJ2ykoGmw"
				, "AGFP6ApUvwi8MkKNtSZScaGM5xgh4RT6XZ"
				, "AGFvP2BHfA3YgUH6SiGmC74eNVDhmMtLw9"
				, "AGFZsAD8zuvN8qEetmoCHkZnmucuKBbiRu"
				, "AGg4wyuBUywDVVZtoDkDne1SgEy6XifM6a"
				, "AGg7c3Fdeo6Fm35DQ6zmHQGbiVUTKbXdCK"
				, "AGG8VqGksRBm183QW43LL4Ex9yuSxWe4Kr"
				, "AGGDS5w94HP4kysgheGTmg1PeTuyerw37A"
				, "AGGFSAx1nTDqHp3Jqfr7qR65rzaJd4VC6V"
				, "AGGJbLiCjLEYRRsFSasyY3vS3BAWMpxrcG"
				, "AGgPd7DXPfvWX195PBn2ahrSobchrAsLqk"
				, "AGgryoTD9iBzsv3rEYfQGmMc1ks2saaaPH"
				, "AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH"
				, "AGHambSnuBvmW1wMDah8GgEt2BqCHm7B1M"
				, "AGhbBB3C7dBUvfgphMajRVbeds1G3Wri4T"
				, "AGhCjgNqTDTYMYLhn4EARp6cYWqe6sd14X"
				, "AGhcMY8VFeqZRkmXJPtDieKMJrvdfUd5eF"
				, "AGHxBJsk8hgFjX1jTr7ExiFWbZD7Z42qnw"
				, "AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n"
				, "AGhzN2AgRm1QHYFnZnk4Q1tc63vUrwe1Yo"
				, "AGi81AP6ZQPViZx22xX6X8KiDDYrfxYyUs"
				, "AGijC5DHveGcKdpyt6m8CLa76we1Nxe2HM"
				, "AGiJcUNVVTW5NRSnSPLfe3QaknfWUxti7R"
				, "AGjcFd9gAPicYP9vHLphXtn2R9dCKWmoPr"
				, "AGJkicsMtxnA6z1cgeHaaHKLUNixiRSEuY"
				, "AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL"
				, "AGJvbrdN2PGC7j5YjrWYt4BzFxH7MsSo7a"
				, "AGjXVpYGrj4ReBhorNxK52t7vhjD4hiHWH"
				, "AGk43anxv8LmYgZxrk6dT9tyUfoYJZ6pHu"
				, "AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7"
				, "AGKcxDL3SXZfeQyNi8Dn7XmdD4tWvpPXJm"
				, "AGKeBvhvk4XGJkeU4mDTjcGjNvBBimrk2N"
				, "AGkjzdDxHY2Kk2GLVke3ThRiWmu6Rxfvh2"
				, "AGKSRAhkfYUGGVz4C8yxTsMFjtsoB8M1Hz"
				, "AGLiRiMQ3UBomMAgHB8KWXkAzZPyKHyscs"
				, "AGLyHp4Q3Cxk1gR8J3SA8GLMBrD9nFwzfF"
				, "AGMdYPcw3yFNRYz8fUSdVXZpBkwfqTFuQw"
				, "AGmeyqLQtpMg9LY8kvN5vF3bXvpPArY64V"
				, "AGMnp19rLupeDm3mgJs9VS9JduC3auHdHS"
				, "AGMpFah478SjsP2umGMzn1gY6WiWw2uXeW"
				, "AGMpxYqEPnqJxu2KBS8DX8opxLGp2ujx1Q"
				, "AGMqgrUmmqDTYH5sfwjAJ6ubRha6B5KKUZ"
				, "AGn2dQdFr9kRWNKsbNi1JKvGaYipYZat8N"
				, "AGN4Cgd3DxWvqpF8oxA77G1YkJ5skAyoXp"
				, "AGn9J1nCpgate9wYG8e9FaEadS4eyoAQm5"
				, "AGnhgMmrtq3M1J73fxr8KkeX4dm4GgZEdz"
				, "AGnMkBgSA3muovsPYx6pcSbQDJ3RzmFmWx"
				, "AGNzfWoBw32RVzrN5FYBsFrSGbTSLNEHMY"
				, "AGoCXDrKv97f8iPMBHbyFKiXcim1qPAhnX"
				, "AGoEdaBmYgqsDsJx6Tf5t7ZVnRVCdyfCoK"
				, "AGoFT83XeHggQXugRF8x7f2BeCjwnNdYSb"
				, "AGoLmmzB1ka8ogCRVnMa5q8s6JobvoVgbQ"
				, "AGoqer5qSjcA4HwdRdxpf2zQcHUFg3Cpdy"
				, "AGoR8g2ozf5EbksE2nxSwwXEubVJbHaJKT"
				, "AGPignGCXUz9NaiviWoRUoBvYJpaiWu5qV"
				, "AGpiWdCnNVxEhak9cp6pXRML1sxJswSy5j"
				, "AGppZMMGo6S7TUAK18rgmSefV291s6g1Qy"
				, "AGpqiWBreVhdc9LuxeJKfmb5E48zJAc5xL"
				, "AGpqNAYF62X4cfqGWFJiAVNLLD2f1487vz"
				, "AGPs1VAvz6HMqfru5EtLTGeQTquyxjYM7f"
				, "AGpzH6czChQ9uiQDf6awZ2WcPx65872sXB"
				, "AGq6SATVSG5M9w8v2YRKmh86sCZR6tyD4H"
				, "AGQC6szX3vVHtAvEbxcmw8Ay5Gai3D9aDW"
				, "AGQNumPvvyZN7bbUHpxz536detrsVcuSSU"
				, "AGqqSMi4yASmWE2jCXcCQHJ2pZ6fD7t7S8"
				, "AGRaLX6gAQ5toF6CkN9a1W8G2SkC2oXkHN"
				, "AGrEWbpHXB2LA3Mynxeagnqfq7uNs5FcxR"
				, "AGrnXbBxfoGRSjZM6CEziD6EG3sy4X7rwg"
				, "AGrWSgeUqBbCLh7Z6Kw5szpxZS994D9zs9"
				, "AGsEjk3stwAtcjuetsP9asMMFSuCgabBCe"
				, "AGSeoHs1JxftT2fzVcMzgXuHJiye5n6moq"
				, "AGsfX232gKxbSgrPdUVELf9B8dGxJAPVCU"
				, "AGsmrRsix9x5bh9cBfFVHfzYU9bfT9sYLP"
				, "AGSnEaBDGjwzEod5x2zPpxchitggkZLow6"
				, "AGTAS4z2Kb6FbZg3eDE2GeHoQyETq3S9fP"
				, "AGTd8kPj8DguZJ5Dy7QpfLt4z7bZJNn9XN"
				, "AGtDsWgRhQpS5WCfYegTeD9KwfjDJcLMnZ"
				, "AGTJpBCitVx2NnpvoiYSXqEUwQ3PQLGfQ9"
				, "AGTkZNaFHbpjPhp1oL4iujRcsL3LSpQSBf"
				, "AGTLAjHwmrT5DP76ka1mszPf6qw2tTznC1"
				, "AGTU9mZpkTn9QyY2A4t7svW2wCreYpPBvV"
				, "AGTVJpXXn9poLfodHJr2aNFrv5bVK5FMtD"
				, "AGtZrPX21aSMp7DhWNeJCyHgoSJVGw5nkD"
				, "AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e"
				, "AGUHdLth4GBzK3Qp7M2G9M8P5jmd9k6bea"
				, "AGUheqpYJaYQFRqCX46U1bzTenKwpaR7wP"
				, "AGujPmAj7wn3tV7nZcsuu19yzw9qpWEaJj"
				, "AGuN2KSMBjBcNifkbvcDx4YsEk6FX552xD"
				, "AGUperFksvVQ2Z9cCoLHsiY21t5JD5XV9K"
				, "AGUrP3CHHdpSesLXPfEfVmjSZBkSzodFcU"
				, "AGUWQrZA5dPRW9KmMX3S3rJRJz86JAxRQC"
				, "AGUZDpapgEguW84NTiF94jABFRdiJLp9q9"
				, "AGv5DDZXi1RyevhKLFUwSAzamNz9EtDwLs"
				, "AGV8FN2nPV99nSu11WQ9qJWEDrKutPHwkG"
				, "AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE"
				, "AGVAjAs1SXDr6oWzcJhGoj4X3XsrbJedpm"
				, "AGVLoMwLCfdjitoag15d5VL6AB3CnHU7vL"
				, "AGvSZiJYBjVcPqACQPvANHJTL7LXswUkeJ"
				, "AGvUihse3pcgci99nKdCnwPy28ksZj3qNH"
				, "AGW5KTs9X47KaoRC9k5nyh9p5fD2wEbU1k"
				, "AGW8yanE6wBXH57JHFh4beKZ5MiM5soeHL"
				, "AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe"
				, "AGwKgEZ8hNdNhHNTo4BoEbcxUVWYFXsWrm"
				, "AGWpMZr8H8u6psvHBQHGYUL3mxpnoYJYeh"
				, "AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN"
				, "AGX3UVefqGxUxJZG9YKHpAVxyWQv3eWnWr"
				, "AGxCj3RnMN7WtjaQMdti9sgRAmtJe19uhr"
				, "AGxkp4f4Cs5wsSg8Rzzdjn81ebTbLWHuaY"
				, "AGXsoT1bWiggxNyztC4dgzReZrzGCy6GG2"
				, "AGXYfbBR4cYpEz3vBZivEcb4qbbRyAp6MA"
				, "AGyEmUggEJutdvdY2spZeLiEjBG2YxDA8A"
				, "AGyFLCT7huk7CGbQp34baLULXjFFVtdqa4"
				, "AGYGyudJpZ2JA4Giu8gWWkJisFoddWarko"
				, "AGyRD4gXt8VZSSRWouDuVdA9D8G3y5tth3"
				, "AGySKaFmX7ZEXFNe1w3ndGbkU8keo82mQJ"
				, "AGyx6QShjvB9reSAQ5gecx4mRSsEFTWekn"
				, "AGZ4c5P67hj5RqV8UCjANceNnW8Eu8T9xC"
				, "AGZ7EXxw6xsanPBK58CihzwWqVL7JTozBa"
				, "AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk"
				, "AGZHFBUjgBn8DZ7oK1P3ovBvRiGrMSTM8J"
				, "AGZVKMuPxLqNnzxGJusFg3NPkKCs38hRgd"
				, "AGZynBKpRtXLw62C2M6AvZTUiyrivCHU6R"
				, "AH15Y7PTPYCLcVmdZPGXApWELW2BLrCiZG"
				, "AH1ejZBRn8nR7PEMZdiBBonivTNMqEVQkb"
				, "AH1muw6YyLTe476HJs7B7RqVFEJgzkRSQw"
				, "AH1pEZ9FhyhgAdiP5BsDg1dogQvjUDFsgo"
				, "AH1shmvdHFsUmGJsz6529SkPDhcrza5Yzh"
				, "AH1sk22PywfUfdrgffLuwaNm7zqoB6ASrT"
				, "AH1VVH4abvfL1SV7FvFJBXVaEUE1QE5SfF"
				, "AH2Ksuc75zpEBh9JMUJsFrDw96H5NK3eMy"
				, "AH2MVuJG85bT4hfYMZ9SsJ7J6NL4Rc3dSH"
				, "AH341LMXqaZmYLGeQ7VQSAhsMXcpjFba6E"
				, "AH37fCfNvALceRUVnnoAP6vp21QoNA12P6"
				, "AH38bLuJ8c936hQEmw3ECbNkG7cwXSKK3o"
				, "AH3ENq7SXMnUNF79ZAAvdujZ4MJriNBQ2Q"
				, "AH3Lde9tuw3WNC2TDZ2UCUavnkFmupeVfU"
				, "AH3mMAMxHaPwfmSdLoPN9CwxZnm7NwjAvd"
				, "AH45bFYEcPNvciV6QYV9gGsbcq45kLSD31"
				, "AH4fRAJYiYAYvacj54YQqU9JUwjmBm8Rb9"
				, "AH4Mzv9c4xgpj4Aei5pM25NAE7wZLi48dU"
				, "AH5ffCZCLY23nadfZUKLT4hPjq2X14Ncfd"
				, "AH5hU4wr6jkYMk5ZtJWvsx6WZg26xLMS7F"
				, "AH5NCP3o85kGZwFhfU1FwScj3cXc5FwJ47"
				, "AH5vZrfNdQ3pLE43dsy7pT4pWxjfqiRHVA"
				, "AH6DQtXqQv8euimh53Wm5jsKJ557q6P3PQ"
				, "AH6hMc8PuJdMYMKL4uUm9PupsGQA5jwsPK"
				, "AH7aHrLb7Enxp8CiM35wvpDG1hDXCsi39n"
				, "AH7h2fQzN6mjy6ege3LG75WC4KEb4Rv3eF"
				, "AH7NMszB8TZv5mSshEF8CEcSnwkHXjtFco"
				, "AH8H2BV3TwaP3d1z6avefq7jJM47oK5Dbp"
				, "AH8iNq9NnbbgbEsB5gat9jRXzxQ3y6m2An"
				, "AH8mpCADVAYRcghJ3WYzW476HU2FBFA4ew"
				, "AHA24sCrGj6CtuHtVjNDY1qKDUMtuiGXeP"
				, "AHA2RfvoKsGS6JQaZ4ZTnwxzFC3SbVP7oc"
				, "AHAHb1sRpdEqhQ9b9enMyxgPQQ69FMhnjm"
				, "AHAMYYpxchf2KKpRLFyfcK833pRQN5qYqp"
				, "AHApyYpmm1nQtAH79F87xWytoPZsVtbrwq"
				, "AHAuPtqVa1VAQv5XpWa1Wer74RQHBj1xJH"
				, "AHB8PSXUE9mX6xWgxM7UB6VDcpmjrupRMb"
				, "AHBCXhkSpD9cbE8ReSwqi4BnK5ZMu9uzJN"
				, "AHbmt7k2Lmu8UZ9Zp7HaEzuo9pvpWTtaq6"
				, "AHBoAnr6GZTRx8o5R5wyWAFEekxZUcAG6C"
				, "AHBQoTzSH8x8fE1dXUEbVhqs6aFop4s4UB"
				, "AHBv8pW2Y4CDcAYMADjjmRmntinmpSxMUL"
				, "AHbw1zmkisAwrtYHvrtiELgzVbsddMAJFh"
				, "AHbZW8Tn48jFyiqFLopo439dCGAqHAyFC9"
				, "AHcf8qTGuYgz97JnZEjDBBVvZ1yEw9632i"
				, "AHCizBCuAu6MqjPywtn34KpypVy6c8ts5K"
				, "AHcknNQaE5evk176yEVdnTVi4biXMuQKLz"
				, "AHCmUSxaTnJXFSyVXj6pAV1WpVW15JBsvZ"
				, "AHcsBS371CDQnEkNKik7SWxQsr8cefQRrS"
				, "AHd1ggsRgUkNzabY8q1PKx7ENDvFivNPQM"
				, "AHd5K57oNnfkrED68zxjKubXv7WxGTajGr"
				, "AHd9bHoKqCw9SKTGGTvWAkARxCgLmGNY2M"
				, "AHDXJDwch1YA1kkA8pfskuX51SwZDwmpAb"
				, "AHDZgioXaADCVcxB6S2roqxPhBXcNEiW7v"
				, "AHdzmhpNcf86hNbFEdjGfedcW2isaXmNxj"
				, "AHE1AoCRqUJTx2fimCfk5KWqzTthd11aFi"
				, "AHEcircCs9V16GkfD39s5PUwk8QCGNCfun"
				, "AHeCrjSryTmJGvJC8tkUGTu2KhtAQ6koE5"
				, "AHEj2XpbWiVsRjiN6njxonCDiJ56QVg7zx"
				, "AHEksfFTFsPKMtGMKoBF5yb6H5hHWjG9SF"
				, "AHeWNxaN96XwBxxsv1XnubsKBmZgU8CR6x"
				, "AHEYrAZk6BHSke3gmLeesRZmZUEc63JjF1"
				, "AHeysEFJxyYSi6XiTZJyLwdTicxdCusPW6"
				, "AHfgyWwBMZkc69RkWVdMPyt9V3aifM4jFT"
				, "AHfHhdymzJepSqCHvSi7hZjgm7NPB71Vq3"
				, "AHFqQovuYn2jekhweeqZv9zJpTq2c1SRgU"
				, "AHfWz6TAtpf7KrxnSjvza8va3EvY4xqNi2"
				, "AHFYpsVbqMBpSdcsKQS9AEHZeWpy5ybbgg"
				, "AHgJYy6cp5ZVBBHvLkMuynQErhPELAyGVw"
				, "AHgLr3Tvcsb1gSa1vqGj3CQdbh4E6za9Jh"
				, "AHgPEnzzGxPsnM3KDaRHR9HzJEUCZBSEUP"
				, "AHgRH7Utuk7uXqQmMgHHtrL8mYf4MCWhea"
				, "AHgvu4inkP15VStqESP4PAqpw8CXgc7wPh"
				, "AHh5g5fCodQduJ3iLjFycxrVRm2MoZo8hf"
				, "AHh63MuRgt9nQQQkhd2jkPqKh4Nk1PJ6jt"
				, "AHHDdQV66JGwYto2nksRFdAKd7k7bLWbxD"
				, "AHHgpKbtinBybhNUqCgwGEqo3oMXEoYnVN"
				, "AHHKTnj7tMA37E5SFC5pvb2zwgwUDjQLQn"
				, "AHHKWM4CRdcRnrN5LB4js2gR1ZPofR1wkN"
				, "AHHm9ZuMYC9PSEg53DCxnbsC3PSZ2ANq87"
				, "AHhNBnK434Li1cc1fTTNWxfskpQh971G8G"
				, "AHhX3mED6iSjoCM94ANj5ndVmuj45L38TZ"
				, "AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm"
				, "AHi3cGhAh29bQiVBk5Ahz5yr2xDKjZR6Gm"
				, "AHi4cn6rWjJJcMjSYF45D7ojbDcsc2weL6"
				, "AHi63kbPXEkGL7k6dP2ANdzCGjKTq2hHPn"
				, "AHibwGjasdpT3uf9a1GmiRDSaqcgdB7D1w"
				, "AHiGpBxffuqFRNAFDVvSJzG9eUY3KD1FWJ"
				, "AHiHwn7FSAtFoFTK1axukX47zDAEifEWe3"
				, "AHiMgh8G7J9kF8E82HhSG7GaLvwhnQC9Mt"
				, "AHj2omzZQ3xcuapRgAG1AfxSbTDrZShDUS"
				, "AHjBnw5tCBNCsRzMP2K7N4tWSQHZJZTVcU"
				, "AHJFhG8n9q2Ga3kCQXV2nyUZYUL3RMsiP1"
				, "AHJfr87joXj9BjUZZN9yCuJvnpbHXa2PT4"
				, "AHk2sRnvnU4D3gRvJ7kxTFb6oBLmvEabZz"
				, "AHKcBoWDDPT1jXsnn2rwwdMT5ixx1NccxQ"
				, "AHkdMEAKUcv5JcJPR9Pn4LwwtFL52FuSsi"
				, "AHKML5K3ccKaf5NK3FTgdDiGvBNWE3roQZ"
				, "AHKpTjNEHfSyVddRWNvSPqqCHXtzgk1Fo3"
				, "AHkW63UkZqwWAthb9E581cZCtk3WbgpghE"
				, "AHkz2GkTYzRcZE39X7LiU7GGEycjVfA9kG"
				, "AHLKmCvZPRVFv5JZmKb5sCRNaFuEBSJPuE"
				, "AHLNroQUALbNnVa8kXY6royDXwcjGd1ZTG"
				, "AHm2tR5zUzHvM27vzXwhcbky5s97HWYLEw"
				, "AHm2wvc9TARwKUk9QPF9wQ6jWi7YwLwZWq"
				, "AHM4yyqkJG4EQJ2uqyzqcnGEB3pS9AmWBX"
				, "AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H"
				, "AHM7cewJvP5aWmJfwkL3ADrzDStqrF8jHb"
				, "AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C"
				, "AHmLgirckHAc4LQhiVzSMz7XmJaTnygYDb"
				, "AHMoK8N1WoxBCLYkc5QpYtszAcxHgsa2Tb"
				, "AHmRdKZ51yM9Nd4U6PKCGFwKMtPWmw2FRq"
				, "AHn17BuuNTjBbH9LSikfy3zMsR2eAGZWGq"
				, "AHN6VNPajwPzjN49pVvxjkNPJMBTTg2VHi"
				, "AHnEGA483X4KZ1k1ZWxGPXCFp5R9fqQt5V"
				, "AHNK3219ZDNsRqZGkSazrUDcQ8fmru8ru5"
				, "AHnwqEENcnZd2fY2H2H3mdarvVarW9ZBQN"
				, "AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12"
				, "AHo5oYqjjW8pm4RN2Nwa9rWgeZe34HNRSA"
				, "AHoFyRoFWgk6aEu6S9PCya2qrPUPemj1Vm"
				, "AHoJBToiDWF6F91jRBMTc4HdDpUNyH2uH9"
				, "AHokHtgCxCe8ySMwVK2hbxCy3rHAJimj6x"
				, "AHp7neEzP9YRGXB8NvdJToPMBuwu46DuAu"
				, "AHPbJjudEyB6EkpbA62ZQeohXcvWRVkNFx"
				, "AHpg22nuz2GrLs3hpuQiZCkW1TybZNzShj"
				, "AHPGbFQGC8TM3JGgaGtoVkRwVK1GNgrJuR"
				, "AHPiLhc3MK7zy2GuYFZzTYGEMfr4W93eFb"
				, "AHPsiozsdtu8udKHu7ARc7ktQnT1jDh6KB"
				, "AHpti5Yfc3a3BThep62rgaeJNrrJdVK7LC"
				, "AHpWkybogbNEaJ2MjcUoMHFD95kLWRqDM6"
				, "AHqcSvVhCpXRhiXLAusihBMEAk9He5B4YV"
				, "AHqGgFbvBuykFr5HqJHqsQBVMvZyDkYSyP"
				, "AHQo2dNEe3vXHEkwusKbBmbeWrj69fBb64"
				, "AHqPxgFXfr7DrXKRFJBgAJGXHkdpigfBNz"
				, "AHqrTjBimG7HMHun3UB7XEmWa2GkkyyhTw"
				, "AHR7Z8FQ87RVXYnbog8HVMT2F81QSRthRJ"
				, "AHRdYxx8TNqUdfQxDLCZvnL8DkjfyRrpNW"
				, "AHrgmCsWB9jGSH1i14A1PHkrzjAYhHoBuK"
				, "AHs2gQ8ojxq2KNbQUNsXDgWwVMRCB6AHfx"
				, "AHs9zvwGBrWwRYcsVCciMtPdWaTUHKJuu4"
				, "AHsfsodrCyVtTXbEVfdLRFnFhsKTK72vKS"
				, "AHsLDG1sPQuUb4skE1JhPMCZ1f7CnkrXwZ"
				, "AHSLEpvqNmBuV9YHN8yystBEYHMucirEjy"
				, "AHSqivMM5zqM5cEsAZVAdxSf2GzhVWgzPv"
				, "AHSUKybnBp4cFo38H3NgK2LWsP3FcBt96S"
				, "AHSV62XjzLdqboZGCvvyRFKa7vo6kyCPqJ"
				, "AHTA5N6BGxyt3dYQbiEBQosi5Fu1KkjNxs"
				, "AHtFeUaUzwqGFzTnYc9yts1gPzimrEH84F"
				, "AHtGYaDtfZuKSHzzL8oCQk3JhwkgLm51Cy"
				, "AHtHqj7B6YQR78GDW8wvzNVKhKnQZJuJzv"
				, "AHtNNAhwfqLtFLRKfsU9z4xMjiLQphEY9v"
				, "AHTRp3vXaX8TS7fv69qxNWkbfdmFVQfPkw"
				, "AHTSuKshJHhrUnZXG17v33hwzoA2qULnrA"
				, "AHtU8SSjJRryT1cMHVZnHS9h6okbjqvrQU"
				, "AHTvUkzUoXFatBpJXoUpv3t1Q4R8w2XWuF"
				, "AHtvuP42Afziirgf5sqLHghPU5ttE79jm5"
				, "AHTyjvCkcWDRaPAKtjZSLtUJpjPxk51rW8"
				, "AHuepSKQuEcBcj3Kbq4YG7AutuK18KtCLT"
				, "AHUJR5hUCjmQhmQbtqVVkpc7fMT8wT6Vin"
				, "AHuKqsZw5nSA5EyCNDiMeDzEDrxTiqnCnt"
				, "AHUmFv9HA6bZYLerVJMbHdm2tU8PLnZo3Y"
				, "AHuPfpLYBggWkqLkKQkuwHVJAt6QS355UC"
				, "AHuQ548NXsN9BaHMjDLpYKYU2vUTSbpft7"
				, "AHUvQ8GozahvABiyjMtqf36AA1cu2DWCrQ"
				, "AHvFAU6NHdsjyg4aAFpzhVbvKDnp7uHgdu"
				, "AHVG17s9Prm6SUkf687HkUUwzvWvKrXkkw"
				, "AHvhmWEZuAFhPGaTyiBShNVxayBxebTpoF"
				, "AHvL72EgwJQ1f5T5ZBjAYNbRFcVaiswSYS"
				, "AHvQELy9XGnFs5vjNSkjbUTTtgjGjuBnNb"
				, "AHVRXCtpAWrhJH8AtJr5vaKWZge4drhcDH"
				, "AHVxoJhz58uNLj1233PbKX93fm2eFwRTYW"
				, "AHVYeQALAriaPpgg91pYuQRY6QirXmh6nU"
				, "AHvzUD1DiYh2DMpgjcmputqkcmqUxVc1QS"
				, "AHW1UPWZxK7Ei4p3QhiXa7gQE3F2ExoTzx"
				, "AHWLBjciz92PYTSi9fFExvjbwzcC4WBfPC"
				, "AHwqYX2t8AWFVuGAs5LDUTjvixqgzTPDKZ"
				, "AHx6KDzxPUAhWn53QCZbMbYp43rN23949H"
				, "AHx7C8X3gcHZtrDTAkeYAGTCNZmaUMpPqH"
				, "AHxcT5hapYkBAJm2QoN867p5JrK86bMDhT"
				, "AHXfkg5YHrWpYUpgfh6D24oWvnqTjMMtwc"
				, "AHxg8VtnDHe5aTsBjgrcUuC68VBW8R1pVE"
				, "AHxj5GNMp6YND7Z9AeUV3oH884XoTJ1Qja"
				, "AHxPPWLtZgTQNkJ6NujwBkHRAwXpU2YB1L"
				, "AHxRYGPBKfQVwnqK8tVgAmHnBjCzpQSujN"
				, "AHxY8odkM1j8zs87FqYWCy9UDZ1EgemZm3"
				, "AHyDsZ5XuJZ1HLTU6GkD8JkCbrG2RDK25r"
				, "AHYfGgp5ySQy3jNuGfUNNQVQAMLvqTy2hE"
				, "AHYSz7XCzc2ef16JGBaQZ4EU9wuLFWPG3Q"
				, "AHYtmMR64pY6ypVBr1tgyBGLTrmWAxCi6n"
				, "AHyU9wDo5F2aiecv36bBVEyDggPhXB8Qka"
				, "AHYZZ6wpQDLA4dMiafqp7pQwxt7XcDfp36"
				, "AHzc8jYegPNZbRVtBiPbthQwqSD8LGzRaR"
				, "AHZe66FxhtbhCEkjPPaAka1UE68eKKG1XV"
				, "AHzhTCctsycq3PMcLPrmusoV77ZkpGDJnc"
				, "AHzHUHpy77XAcDtrzgeA3S1kvV5p7VoibC"
				, "AHZiA99zdjGvUFi2xtP7u17j98EdXi9KfG"
				, "AHzjT1mBfzG7gTQyzknL9c4rutVafjKLng"
				, "AHZLqKvuvVGYQusn1mibkEgn9aqdWtZDKB"
				, "AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj"
				, "AHznC1uXHXwfM3NqajHJddrMAj4YbiriMs"
				, "AHzqfkT1jtXs85aKY78oUteLaYnJrofkZJ"
				, "AHZVcttvmSyhgrNESnDw8ESd2TenK7CCBH"
				, "AHZzURMhcGiJ6WLAZQJrTE7s1mDJt3fH2L"
				, "AJ1BshBEHEX938fawmZecdQ4zCwrXvYEHz"
				, "AJ1FuUEmfWGE16fZA9izZLCxUk93dJdwJn"
				, "AJ1TLf5QDxiqGfMYkzCHbaPv5uSbcHQwhn"
				, "AJ2CPUg7S3JFb8DhPMnN1VYKfFbXA72bfp"
				, "AJ2u49W3SNFXMMohXFQK4VX4aYwddCCHdx"
				, "AJ359nzBDUhp6NNqSNyvR5QYt84iRHMff8"
				, "AJ3Fn19BPqAhzu1FG4tawRtcBarVRMij9B"
				, "AJ3GmbwjBEbhSrh56PzzpXzrqY7ymRjeDh"
				, "AJ3Hxkr6Ge56rMSrePnunP6wh3SvZY9XFb"
				, "AJ3HzyM7YQmYQDMnH2pYdcJiLXCTfWTgrE"
				, "AJ48BZEiA6W3fAyKTELA9T7pcUBhPqra29"
				, "AJ4BioeATKFYoWxo4uu5zCeWzh2fZBGq4o"
				, "AJ4kNsPn2haQKZjbtd1zFjhYeXtg811xrP"
				, "AJ4Mg9WiURzbAftKNUEp4hW1YzpcFMpVAv"
				, "AJ4QZchEjVGDHPRgYckJPBCdry4vNzTiz8"
				, "AJ4TH9w7udc9Y2azybNpkwWLVc94egyTZU"
				, "AJ566RBTh3GbgxspBMEV4sHyG2ZZDfVRHC"
				, "AJ5gX9HJwdayNpbwWLmtSLBjejRWA4eN7U"
				, "AJ5kpUVTVk8Xtuixm42y7CiVgQoCGamMni"
				, "AJ5NLrngsV9Qw4frjNS7LRwPi315sm5FZm"
				, "AJ5qkyY6T4AfYaTLUbxULsDwggYzm8op89"
				, "AJ5rTzx4PvENieYfpyR4odgyqbnbwhZTsD"
				, "AJ5vBUh4tXNgJ3esUUQK7iJBYm16KfJUxS"
				, "AJ6gqHWztLhXkYX2gvpSNm46GjK3sTzjCU"
				, "AJ6nzVrVyHKeztQhy8iiDngAraApZWQ42R"
				, "AJ737v3UXkctoxXqpwJyVGPUrPXdXk7LMZ"
				, "AJ799oByNAr7FM2EHB7hdi12K8bTENLvhb"
				, "AJ7E4N96WwaVrv3k3d81PVwVUR4KpTRVmA"
				, "AJ7SrsaefbA4MvpkjWjHaVueDiDK7LVvin"
				, "AJ7unfqqdufW8A7HrvNQS65VS1JZ1B9MuX"
				, "AJ7WcXMmRMfVFMwHLoP9sZgcmBQxHaSrMd"
				, "AJ7XbqYYm5ps646NmRXY65kpdfQtsFWdZB"
				, "AJ7xMNeRkyiwNuXjVUmYjKFCNfKgX3ViDL"
				, "AJ8ffs9xWMQEsZpVHrRgtxgtGSHD8x44er"
				, "AJ8jYaKGC5sPf4THtoh7JVoGr9NTAniuMY"
				, "AJ8REqM73SmDHspMw87KBnj7AdZdghGnRB"
				, "AJ8woBC4Ci3RMHQDN39iDKA6pRqvBonEgJ"
				, "AJ9MY8Wh5uEUc5AiVE3BWF1pXJcAUGpRPb"
				, "AJ9vWrpBhbJMNU4C4YtrRMqNJmvsWHZNbx"
				, "AJ9XoboLYzhGcrrkVXdtyF43orM3LQX4Ap"
				, "AJAAWsEcBcWNmuqGiK8f2YSNLnX4NprX8G"
				, "AJABhxgbrZmwtE6oBVv9MFjoJvahD7HqLU"
				, "AJAbmRCJo3QApCkEsf1emWmL4akzKm4tp7"
				, "AJabYUcqLYmodnTbGx6stJxduofNnJL8bC"
				, "AJAgdS2GEW8JxSnroE2tTVKGsBxnBAYB6H"
				, "AJaGYBbTFTsZonDCnS3CWT1RZukT7kLuX6"
				, "AJAih3aoCq66u7CWRjDdZEQz9kNzP7cHNd"
				, "AJAMrC5EjzD9ibnbfd8DPNkUfdSAkBLVkT"
				, "AJAQn18vkrgVFhriGTd3NUMtxf77aXxkuT"
				, "AJAteTeVM6qdktnbiGZsnJazAoCeA9kapp"
				, "AJB41WpnMcQqzTiXneBKPAqp8fbiX2qn9w"
				, "AJb4TW4jzYi8TETLvpjUxFv2iz3cFj5rmJ"
				, "AJBBSuxzsVH6JoKYfRsjZa87JSMjnVtnxM"
				, "AJBEtVwkuedT2tQ6CVhuuRSusmW11Lc4Jx"
				, "AJbNPAxy4XpouNh8FW5dhR9vZzTH58Syk8"
				, "AJbspJNMUvbdYfZqxPSoEiCyEdeu2SwSB5"
				, "AJBtuRnTdUAoXYt1yJA1RsjkGp7uMhEf9x"
				, "AJBxgEk9ZJ43pSnPThsxPNr8eqXUaru6AY"
				, "AJBXNK3R6oN2LgYqqawVfAuXnBrSvVMLQo"
				, "AJC9EPu8y8ayrd4a5GmLaMiRzKc913pmzw"
				, "AJccFEitzvBrCMhgPyEDjDzfJsyzrKbLoC"
				, "AJCk4BdeaiZfMwoggqTXdjNRXZnWmt2uwy"
				, "AJCspNnqKXQhKQTBt6p7JMfnkAALAKmaBh"
				, "AJcttjgiDXEh2b3mptRCh4hywYSdw6hyzf"
				, "AJcZNiQF74XMtKPc8KxpxnZwRuZKvtmhtY"
				, "AJCZXn3RVdq4yTZ1NKe4FGZV7wdPN8tx9a"
				, "AJD8bQJhe5caGyRre1jzXoQMnbCNvvm267"
				, "AJDFYKwz45uW511MCHXrRZPRemZkbMgW4C"
				, "AJdgXTZuKecyEsNZxu3DoDYdwdzXRhJHg8"
				, "AJDorwvCRDbiYmkLLZ53hW82EYf92Ho2MF"
				, "AJDruqq4Km33pJPHpKicUuLrJTM5qR9EBy"
				, "AJdSCwpKrwXtBuKo6ifL6GJaY2MAwD7QKt"
				, "AJdseYeTxa9A77ncDPjvNSSeprMpTZARjU"
				, "AJdUGr2a3uEya4qjnavZSeF5AVU2WUgLSD"
				, "AJdvX44Y7Hgd9sxANwiAWTDrDAxmWXmq8p"
				, "AJDVZXkK6rhg91Ywx7gWQQETRezBgxhhDu"
				, "AJDyVAwMmo6RL1JF3L7FCetWS2VRM16Jc9"
				, "AJE5khm4KcxkCVMt3kixPydcxsWNzUUEtz"
				, "AJE5kLh3KMSpQ2j7qxhgBP3Q4bu9Px9DXd"
				, "AJEej9mMUuTibnzjJGiN9Umhsz6A8bePyZ"
				, "AJEjNVo4zzKBq5x5SoabgB9d3EiNrQ9Hhj"
				, "AJeRVW5QsbrGtvZSn3MgGg56FLJ7GyMMqG"
				, "AJEUSiTkBTsdkCYp4KRVuGuHikV167cv8s"
				, "AJf7UyouAvmm1T4wBXJdKooVv8V412uf44"
				, "AJfDKLaSsX4E3x2pDYuL8Uy2UFc8WA5PP7"
				, "AJFG25vgdgoJbatRsrCo98tgC46NdugPbe"
				, "AJFPjriwcU876oQkEV46dE1aPLRnotzGfM"
				, "AJFsGqeP34x9zHqx9fNCWge4rZEaMLmAr2"
				, "AJfxFKBSiueMQMqMUBKBt4KvqBGZwvXgoH"
				, "AJG8AU3LLjFwC3d7j9vxo6aQWa9AfDYxWq"
				, "AJG8xDKBRqvkVCx3uV35Snn8PpwJKjXYzC"
				, "AJgJN9TuHfLPRYnFMSCezviDDJov1Xa94R"
				, "AJgoALGezz5YCPX9AVL2QrSKCSbo5VDTSx"
				, "AJgroYH62qjdrB5AJRnfUUCH86AqWwNqbh"
				, "AJgUQry3oKUv3VmKrDKSJ2iKkQ2VBHgdgJ"
				, "AJgYNPwPSgnRmYh5HHuriMUTRk2H5SYrYk"
				, "AJgYqMKLYbvyAvE53eGJXCiyd7Et5RwV5r"
				, "AJGySWq1P5ZiyT1UT2Vntja5GBEUt4trrg"
				, "AJGZjxvxmctCE4DM4GErAhXXvbQt1nBPDW"
				, "AJhJmXq5h16TCd22tWExn1RoYFRbm9QS6Q"
				, "AJhkZczpogHYoyVQzTGngmkFf7zEKUyDiY"
				, "AJHnWkYKmKium4uvc2KRVJMKdi7o9i7Rp7"
				, "AJHyekw2QLW3dtN6Kk5rTgpctQET48Bfmn"
				, "AJhyHtzQLFhzRFChi8fFVwPSfYuriuNkcd"
				, "AJhZkVcDcpZcWEghmqFuB9YuaFw75qsHUx"
				, "AJin4dikP3qE4Mt3h8c2TcujVr9WwpJJp7"
				, "AJiRwpoSX3JQRehNg3bMV7Lp7jesETTH72"
				, "AJixEbrEXyDpJAt5FfFEUzjaKXLLTnGWx8"
				, "AJJ5qiCR232UHUW57f4PMNMTi1MHqgao9U"
				, "AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF"
				, "AJjHUDYeavC1BzyyXx53hiSmwkzTLCmYxA"
				, "AJjMphtzj492dTZHSyF5YjXkNxKuYkAwmk"
				, "AJjrXK9awb8fMA3N7koqRXqDqsna6nWqhn"
				, "AJJvRp7aLZH2rnvmRJrVGuKKR3p2MvMmEZ"
				, "AJJx1gtcWFuWeUbCjieXUBSs2qTGfF1AQT"
				, "AJJYKvpW5NattjrUciSZmqMmKG1rrBeMbk"
				, "AJK92NKMvFJBKWgQKAuWndPuWfN9LVGVEL"
				, "AJkbUMR4SoAGta21mdHbctpnSFdpuGic7Q"
				, "AJkHC4dqN1i97rJ5js1SzXeLpukAFWgMV1"
				, "AJkhjVtjQkT8GLYycG9js1NwXCBoj8sFsT"
				, "AJkTbxB2CCuHwApFezEe7Dde3kc7h49ZwK"
				, "AJkUN5ogU324gkULkM4SDN9oXAxGYo9hCz"
				, "AJkXytipKWmKL2u1You6HX2Xv78DuTBCxH"
				, "AJKZW1RtChi4UQJz5NP8N9JTdp2JwJftDi"
				, "AJL24rj1CDNu9XLqzdfsTyCZf9TQbsJHsL"
				, "AJL9U9pgqVS23J3WPwpQbcdrTvpR71vYYy"
				, "AJLtMW4zFG9zaguA1CBoiGN9JkdHKwfH87"
				, "AJLtZKsoFipqz6uVkTYXbp2ySWxJ4h3wCY"
				, "AJLY2MR4VARzDErRd782bPu47bHxaeXzcp"
				, "AJMF1LwJpM5UgF31PUanBbMMQPjMkYXGwH"
				, "AJMGTA934Ekw3Ehsx4n5HpKrDhLYn2WAS3"
				, "AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx"
				, "AJmSJfnMwzA8DYA9rS6hJhcmdPAJe2Dj3k"
				, "AJMuxhBoRqrBiCpXhtMak8oc5yxRUW3jnj"
				, "AJmX6wtkAJUotyy5wgj1ucb6Fhm3W5HzG4"
				, "AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6"
				, "AJNgNDYCVdjkMzmN9juGanwd1gobZVdT7u"
				, "AJnhVEHdxDKuCXEnBpfXaqfm8bBSJKdSjt"
				, "AJntHAjeizAQBHdP8FNAMNvB8WHnGrs3zu"
				, "AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3"
				, "AJo3pq2b73zxTXScr4uLR1NmcXZwvHoTiA"
				, "AJogqCm4DkGJUigMG1xiactEhPxJmWxQNN"
				, "AJomqFNBRAEYKqgqS9pA24U2sM9HUrER2U"
				, "AJpBdnSQ7tHSje5gSDoBUcT887JmxaUSzp"
				, "AJPEGTj4kobuMnKA8M7kTrnd4qdsVyvm2S"
				, "AJPKVca1hh1os3UgqSNsTYgzzSiyjEqyL6"
				, "AJqc7iUxq9Dho6DxhrFZvoLDVb2JaHc3ms"
				, "AJqGH2eAt8A2ssgpiAcEN3es15xEYzhLwL"
				, "AJR1QcydExaQfzEHRKB2dPHW1a6y29rLKf"
				, "AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4"
				, "AJRKtwZ4JZUL6qknvmuR5FFtv9obH5JGhT"
				, "AJRscgip45wiTiufJPSaiM45FNSzzAsRuV"
				, "AJrSe3rna1XX3yJ6hPTjzkL8JH8JGBUnmA"
				, "AJs9d4XhULdYJHxVVgV7PwAwBoNeGXw4yU"
				, "AJSDHYS7aNzN9rz3svVLaDWoN5FieMFeZu"
				, "AJsh5nPaU48B2FPbGtHgs5jxmNwDTQQc6T"
				, "AJsHTPVsMKe8MH9FXrP6zJerWw5zJSks2G"
				, "AJSJKnm8DrkS8X763zFjhMTqmbFrDZFZHs"
				, "AJSqBaCjSBH6RCFbnyXWxRR6X3cB4Be5EQ"
				, "AJsSJHS8LVS1sQBKJ9aGQziuJgijF5jdaD"
				, "AJsUKGneMLTAMZETFKg38psu39k3Svc5o6"
				, "AJsVwurN9qyhuoeZPqNaeCe8GqTRr8qLwQ"
				, "AJSXGFBRKw5y9vuy1hTYkb8aygvUhUbAtV"
				, "AJszcwbfCsinPCp5H1EBL2nV7WuSysW1cs"
				, "AJTa1ynBKJ5P3xLu2VdLkhrcmiwWgRajpa"
				, "AJtaxojj6RY2iGiGbJd96ZWoYzL7Gicj5F"
				, "AJTD5cAXpPwxNcqYXDPr4GG7Ndn3U9RHdw"
				, "AJteEX6bRKTF5gNFjUo9MSQurangUt9WPE"
				, "AJThbT9Q4z3DGs8H1VaBcG8g2UYBccha72"
				, "AJtmN8hJSteX3ATuTAmLNYLR1qFTmYrZah"
				, "AJtqtJzjN17E1FUqmrpfpAjrrWcmGodZQr"
				, "AJTURhcnCUjz36rMKBJU6zXkRYNCXZ8Mcb"
				, "AJTWAgkfEs5jY9wgcC4pDtg4dFZV7dQEmc"
				, "AJTWbrS1GxNYRYp6rDJUcbPZXQ1LNBXCXw"
				, "AJuAAJyrfF1ywkZHDhjbogJKr17QLL6Px3"
				, "AJuBNuj4fpyW3vrwYroreywrSasfUjuzvb"
				, "AJucsJcY2cNxMZb5zK2g5AEZJJqa1FZ8qT"
				, "AJUpiKx5mtNoANFDaJZEWDfYytf9AnTb8V"
				, "AJUt8QKfrhQt6sCcxJks1kApiGUFG11nam"
				, "AJuX3P4Mh6hMf1yRPT2oxjAYpiJjWJSfPg"
				, "AJV7PPvpfWasdsVUAea128bnoyUzmBmpEz"
				, "AJVJ7nkHVD791VwRxVYn4viW3re34pz8ik"
				, "AJVr4P6TUcVJwZzP2F11cuuhmTfAAYrjEr"
				, "AJw51w5ZcAxSx3F4szMx1sWB8SWt8GD7ME"
				, "AJw6qaZxytLszeUnkomfbTj8m7oMwGhmqR"
				, "AJWc5UQ6gPbmAvr7iJpLubvYPPkfzWB5Ds"
				, "AJWgNSV54gbp1N3T4zk3gad1V1TkR9mgWb"
				, "AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW"
				, "AJwR4yM5gwrJkUotGP2qwLfS2Ks5ykgYig"
				, "AJxjPSAeh8nW21Rz7mg1kHEtdC26FgUgxM"
				, "AJXkZ9wq59uwPAh8U7jf8GnYta7ug6Js9J"
				, "AJxQ9VnA9HTsD8C2CPPELHw39tnhZHzBqR"
				, "AJxTDMtwdfuVUtSxuGm2c1paN92edqkp57"
				, "AJxzK5xqSQvfkjYfxzzssQs1pRpzyLtSY5"
				, "AJy54mYfkhKEpUCUcdR33fhZJ3SsDpzvu4"
				, "AJy6rbS2NdoFenPwHfFm2qHUVoZhd88C3c"
				, "AJyAKEZxskZ2pt8D1nDo3YnaNZzqKbVuLB"
				, "AJYbfqtu9FTw9hzP1x3kcQuSNUvAjYTRsY"
				, "AJyBUbXUYQj28qwSZzPPQFiagopwE9sG4K"
				, "AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr"
				, "AJYfcQUpS63ELsGodGVBsQxokGpQBtVsfw"
				, "AJyqSpYiBvigKZU5kCajEwcbmJSBKFv88g"
				, "AJyVSDNsvFakRrV5DE1AzERBvuXZ9X3xQY"
				, "AJYY6oyEZeMvc4xPLGyrkeDgAdhXZpe4Bz"
				, "AJYZ5sXas2TFXsVhFFKZkoMCi9XddNvraJ"
				, "AJYzzBZLTEA9M6kRgsHLEg3gs1JZCRFLgK"
				, "AJZ5SsH7nbQdnPt8pWcrTpRebDjUyVpWHh"
				, "AJZ5vgrwZVbNKYbgY7wLbnsPAQ5F7KReCY"
				, "AJzLBJzX2NguvtyZCkcNCA5amGScf5d6YA"
				, "AJznv6UJMoJFrA5ZWwDYZDnhmJRn1LSQ5C"
				, "AK11VZG93oK2oDT49hdD1ULxbQncT9REgF"
				, "AK1ftowhZzgjgoTMyjqobNAR1zir2AahR2"
				, "AK1VrQuMxyLsnFwfoz9MfeGU528ukAHdyD"
				, "AK2FW48KzvGjL4X71wiYQYKxcNX44pWfwf"
				, "AK2mzz2GLVpeHR77MnYrY8jSpZgtUpQojt"
				, "AK3dA2tzDg6jniJuGrgX8ENAoQbRWH1DS2"
				, "AK3p4JjMGfZ33RcEq6VhZRm6e9sj4kFQ3n"
				, "AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh"
				, "AK3TbFCz2FJx8Z13KX5UFKtRm6XZrctc18"
				, "AK3W5GN8xXRo7Zc85AWmyZC8NHFnuEBNyy"
				, "AK3WhUhYQJeBkfSvR6vSQaUDF1XtCCSjdb"
				, "AK3z3r9NwRLZ8NojNB4vjkXbcDoeRynUeR"
				, "AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4"
				, "AK44my17FhpN4CAySWWN8THcCUNqvV6AY6"
				, "AK48SmzvR5JJykd1H51mjXVKBXBkeFCG2Z"
				, "AK4fzB2ph9xUXAuhYjqcRJ9qq436rm92HC"
				, "AK4rXL7u8QS8zNYBX56h3K5PRRkHWoxJ2i"
				, "AK65akvjxkAMh8kz7pHfYLRHRf449pyrbZ"
				, "AK662KpeeaCDsw93ekxFR5JyqjytCySkMf"
				, "AK66YRN1CXVqu8hbUwzT3jc45RZA9N4DMp"
				, "AK6a96YJhZmm8Pz47SqKrMDTiRHBAeo6Mh"
				, "AK6apjtgVv9KEZ2snpX6LEJLMjStoVps4P"
				, "AK6Fvh4RvLXBDd8K4Vdj6pc4B2BVhAv4Fx"
				, "AK71BugaBucXtwjCfRy8qBEdP5MDhQmhMR"
				, "AK7hafvMyzpzuPdgKM9N8oFsCMd2iWpxAd"
				, "AK7hQWVF4g3p8hc8Lt38ukaZbxtrtYq3Y5"
				, "AK7Nygbk3S4pMia6i3io2gjw9zyyTg3dam"
				, "AK7VzwZqS16PJveN28eHNWMEnZrZShg6ik"
				, "AK7Y4ZViENwwVti9bFRhJ9k1WwR59ddY58"
				, "AK81X1xeYy6xqpuab2zVWfwjLx6kmDAgP4"
				, "AK8FLRQXhWQwoYCLPwKpSvshqzfNp6YrTE"
				, "AK8PmvHAmiusfAbMGtjcVTuaDnMbRWw2gq"
				, "AK9ciCkXeXsCkBAQrZmYvovGyKgXAwQTvU"
				, "AK9DfQ7yEouisZxR9LmR1pJCZmhMXHj6sc"
				, "AK9g2TMEW7mvFYVBLZxofAJmRn2V972udN"
				, "AK9qoYn7UomienA4dqnKhdtAWPhudUq2Cz"
				, "AK9XGDDDWPhkySzwxnXwC1xR6RKr35nQpj"
				, "AK9zqW6ncVRD5YZ7LY6pxywUBuuLhVSm1R"
				, "AKAJT1PuoeJNjsvEwTo6XCPUzS5AySayoL"
				, "AKaLnf335G22hscd16x4sXXTgVxHykVdfZ"
				, "AKAMgZbiEDwrtFcjByL2wqhaMN5R7xodZm"
				, "AKauwoZMmPoPbH6nsFH8yuV5JYB2MHZ6YL"
				, "AKaw2wE7LFENKmAYSW8rs12zCRZDsGnVCd"
				, "AKBHUVVhscDudKHgqn7VK3xpymdet1gD6p"
				, "AKBXTUFc5aCB9crFGB7trEqBMYowv3NGk6"
				, "AKBXwUggniNcrtqzuS7tU183jKsgqGbBWJ"
				, "AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY"
				, "AKCbn4ow4TDRamTnS4U7AGEoFrDM4TKXqk"
				, "AKcbPAQsqCTcyFjQmdW2DMq3my7MqsPjPZ"
				, "AKcrQDa4t8gYReFCFM4XDdkfNCsow4TjTc"
				, "AKDHuxNJrVmJgSanvyymB1xxRN48eT1MJF"
				, "AKdMh2cvoSaGwtYRL25upH3Y5e3Pb1Knss"
				, "AKdMiqNcdjcfuEZg9fRhgrpBn74AGFceif"
				, "AKDY5uuJUXPocjiWjpLGF9y8J3C4KWVGoZ"
				, "AKe3Xo53gbr6ozSPeAUdfQondsvPfB3qoy"
				, "AKEkdQUgHMnFt6rkgF1s6KaPLaJX9iWjFw"
				, "AKetUYUPe4uRiNsKpRUEoZcK87ZehnrJ3p"
				, "AKEve2qS2ZqghozCW4W6sheCFi9SJdWmET"
				, "AKf2A6jwN8QJm1HmnQV51kpoQQEZXBgmZZ"
				, "AKF6h2QP8Cbs2Hf2bnhs7iphavud6sdrL7"
				, "AKF9eiTfeqkkoYE6BTwc2jvYH3GcXGyEvE"
				, "AKFHbbqLwAUsAduHCbFDG3EnABm2JkETXt"
				, "AKFPKFP5mf8B7ZY7KgpMRFGNS6yPimKEh9"
				, "AKFycC3Abay7Rtoa1yQPU1YYYB7U47tEjW"
				, "AKfzMKxMeYk9asV2pNAmfC82z8x75qwGAM"
				, "AKg1TYEBxJqVkt23sx5d9cLujkhDGuEiww"
				, "AKGsiS2FjXZgfX9JxZbfsTcV1dzat4yd8r"
				, "AKGvMdgsQ7CjVbuSWA5aoQHqnhsdpsqtCc"
				, "AKh2HNyicLwgjRfxq2Gbim2hBZx5nWagAw"
				, "AKHeS17TWb6SpcTqX552RWV7oWFYMqmbyN"
				, "AKHFD7XWykkzzArjh4RqbUnMNABkSFpqiz"
				, "AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz"
				, "AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB"
				, "AKHKDsY5YfZD8JWt2aieBaT2xfFWKnhrdw"
				, "AKhQdCfJoJ2QoBYj8GhHDjMz6oH5N9SCDF"
				, "AKHqmEmAVv25J86v11PJgHyR4UQPRoCwtz"
				, "AKHSjZiHAJLHji2cPV9fTSrn4DEmtHcG7G"
				, "AKHT1WuYdC5aKEUZQDGEv5qynGiVNsHVcm"
				, "AKiFjJM3NjGDpGeVrTpo9RjwPWd3etDsUL"
				, "AKiFoBZHEVgmWSfEygNpo5VPYe7Cg1Z1Lp"
				, "AKigYSfzqsDBoXBGEqXUP354qPdZQVPhqf"
				, "AKiqwYB9grSjA5LtKZPjC85xSXKtqBqJCY"
				, "AKiUtLkqaSvMhxsVszdzHe7vyAaBzX65qv"
				, "AKiWseH7i8ThyTiPhbGhYQQ7GNTEGLrfBR"
				, "AKj88oSPgfKdkHMctLWuykVMavviT1V74v"
				, "AKjnfBbiJMC1KwmZar7YQfpp5u21D6NPvn"
				, "AKjP2NN2YGRYirwfJQFRgMrYXc4AbjA2uk"
				, "AKJQDaiHf5UWhrqJMY1eZcwkjyVRzFpcvR"
				, "AKkbaSkwox2ZPjfeYVouKabKdbFNjBWRjJ"
				, "AKKctLcRTGVC2bBGcyPCGd9QeYFH7NhGcU"
				, "AKKjm8pCSy5feTSPpris8XxKDAHQQ6FUbw"
				, "AKkM9sb2GW9n8k7sMJpTWYyXVTRsbjtCXo"
				, "AKks1grBhzRXD7Xm9oVjSVtZ7p7beH2c9V"
				, "AKKyCoUGCAaTA5xSnVWaA2WpaUE5RoESo9"
				, "AKKyDAfaAnWqYWwcPYAwwtwqVCrachpi44"
				, "AKLbFc1gCvYBLiWF8FpjPMFYkci15yueQQ"
				, "AKLTQSFapZtmibvYRbfTQHzr37Uqt9vw8v"
				, "AKm4SFCjwRfkamfz7ozcEzdduVwL92RpjN"
				, "AKmborM7RaW19t8QsZXYNqf2BEcA6HhoWr"
				, "AKMbtR9reBynvFqK87o9NgkqYnTBSD4sUk"
				, "AKmdivcXgqb72qFgUttfQtzj7LQT4bXZKm"
				, "AKMnNx9DXUoPKsJKT2CxDPr627gGSHpmEU"
				, "AKMNPV2BQcEEWHGKAqLEXbobmBK9KYa7L8"
				, "AKMzLHLdrdZYNq8npPokQqeu4D1UEyy6yo"
				, "AKn1jnmc9bvK6CohAnUFC964yrXNck1Vzq"
				, "AKn9BdFEj5Ycrh3DRGtdR8SQLwy1u4gyQ8"
				, "AKNACD4TjFyfy6EqR4uxxhFkDRHrWxPJVZ"
				, "AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW"
				, "AKnmCyg7SVdYoXHryS1nbdMNHYEbmjfbAU"
				, "AKNQWmzpqonKJEDkxKVoj15J6s6wMXMLvM"
				, "AKNSqXxa5iMzFmxbHRVS9ZZYU74MtRq8ki"
				, "AKNzEAMdqwwrEKF6oDnYMWryuVDGDf1DTo"
				, "AKo1xcy9Rd6LngbYxXMuHv6ih1EMCySGCk"
				, "AKo3QBSNdc9gLmLoS9MDaSet1u79oegLyC"
				, "AKohjmVefS4yxcwWu6i8qqk24KmRGL3gAE"
				, "AKoNujeJQm4pyB82ofqyCRvT7fEBvazT6q"
				, "AKoXC77UUr1811Sy8gTCvJoREUaWokvrjG"
				, "AKoZtaGSAkvsCss5WcHyt1gxeGvmmVng9i"
				, "AKPG7AHvwzSrZsPGxRYgyxNM5nP1GtFEu3"
				, "AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK"
				, "AKpmtmuyyVZYaKtviQsTKeQw5oyoKDE5fk"
				, "AKprFqGqSiVTfXanAMkHFdiYXsYJqpHHjL"
				, "AKPY6ZG88cEXkrRU8J6rnaDARHZDAZbKmq"
				, "AKq2xi5m8mtBg7mYtLgUqtKpzDmdDoFr2e"
				, "AKQDXejoaQpFZMjqA8rWi5vRxM11GC6XFQ"
				, "AKQfcr54TnfiBJQVSzYtcidP3sV9g4uywB"
				, "AKqpZEHp853YF5aGS8v6WdaTAnzwUXeekJ"
				, "AKqrPhLasqiy7FLMnkUWbJGdCyUvHf2qkm"
				, "AKQrR789qa1yoVbkm4mBoMzwQ87pKYnE5m"
				, "AKrKxcSmvmy7YFLyvYigWCyi7MixSpGN3R"
				, "AKRNTxP5Z6S9v4ARwkEHAGtEh2iXURWCbB"
				, "AKRtZxtVKsYfjXcdxP6D1ZCk9GYAfk3N6S"
				, "AKrupX67vEk6oRyNhzZK1xvdPdEKqikFV4"
				, "AKRxRoWypvEemXteJARP2hB7Y3Ht7fKAQE"
				, "AKRy8oCchHykHJHA9wyJgtoty3hyHqCeqC"
				, "AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek"
				, "AKs7VMYXghNXbJQ9QE3rw6jCUd8srGhGqg"
				, "AKSDLYCFjXeiBXhUWGNho9Cjw2Dg4gnP9S"
				, "AKSGPZP6djbXpmqiizv2LkAXgSNYJoY6ik"
				, "AKsJahKsuFf7fZjnyh9bW5xEmkq5P4iK5N"
				, "AKSk7sFqzBT57nY6FFXnN8Ntzay9zqVPyw"
				, "AKsWreVtCjH8A6Kh18YHABCze6aRjTmfiC"
				, "AKSzDbjQ46MyyBETcABwqULhsqp8KsmayW"
				, "AKTPc3194RRuWXibE5wWvQSXWSQLfR1V7t"
				, "AKTuJbjygs9mC87kVFRiB5sV5bTXJjA1G1"
				, "AKTxnGvnU1cC3uu9sL3ekNft1eM6DTbdqz"
				, "AKUezKK4dKK4XgLWMvk4Sqs1mDaKvC3VkA"
				, "AKUHiqDoXzsb61A2F7Qyfhc3RqKbSQuLiw"
				, "AKuNnvJGEfn3JUzT1jqxMyZzDeFwkH8z1C"
				, "AKUoPXWYVnAXgFFCeQmF5GmDea9dd95Her"
				, "AKuRMZgc9XrgTPbntHYBzyATVfwwXz8yeZ"
				, "AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP"
				, "AKvECfLA8V8CRNq8e8d4ppHRoa1tmS9LPx"
				, "AKvGqpoaH92LStoWvYnjEQEPnUFvwK2iJK"
				, "AKVihsgAn6mCFGGWA4RWr9QFULmmUEkTrj"
				, "AKvL4B67yxq5aKbJnxJR5b9LFkEHcpa7DM"
				, "AKvmYyykoNx3CSQ6RPiQHZEL9gXcg5zhSv"
				, "AKVqSNPZcY3R3ic7iffbTpZcCG3wiNZRWX"
				, "AKVW8eyk5oc1SLAxJ6EaYCLSiAj77hizeJ"
				, "AKVXz1riJ9Xq8fogZpfNKmx6RszBsozjuF"
				, "AKW6U9nM2dRZH24WhmsX61Eo4oUyhEUPbV"
				, "AKwAGHVxZzfEGfjaUafXsc4jukZ8AuWvYg"
				, "AKwBLifP9hCSFwmBL2LBvbTNjXQi9vcJgm"
				, "AKweYZNYddfiyjTcd1PgFedDgbPZTjiDcb"
				, "AKWg6KXSTuyApudB4gpW1S5xvh4gJbGoNQ"
				, "AKWHTK9GWq2BaMfcjDpVoxGbrvNd5pvQTZ"
				, "AKwjyTCZmfmYgZLdd999VuwCsNSf4o45RB"
				, "AKwoQizg4eTRBvMuBJmDYY7TCNJaSjxJHK"
				, "AKwqkd6s1jGk5a8ykY2eSGSgUSJ5tNeaCo"
				, "AKWszbBbhtHrAPsVLYBU9At2n61ZhbFYKF"
				, "AKWY1JvnRrCzpdyjTHWuJ6N4uKe69SabLZ"
				, "AKwZXBHGrS4Pv5AkxPP2C7YqfWLyEuTNzA"
				, "AKX5sBgdv9K4mn1jBor6SzDj7irSuXYrYb"
				, "AKxcD8ETi3ATa3Vxp1koFDoC5p2ttN9QND"
				, "AKXga41Xr9xEUS6BgZjW46d42a1yyGPqic"
				, "AKXP5dV6MewUpeaVjs8kmHFThT1wadLRcJ"
				, "AKXPCdwjZJWMt6ehpLma2nfX5oFVJBpMEQ"
				, "AKXUniyEKRcj3sjNeAU614h4uiVWnHLQiV"
				, "AKxYMbE7nGJrNQSTpLZfmUFFyD7fVB5B8s"
				, "AKxZpcC8JXTZ4HmvgZsF4xju1Te6j6pQxq"
				, "AKYN4shbcA7r9HPAttKrpzaq7oSfJ6MNmL"
				, "AKyRWnbSePv14f7zb3m21w7EiNWYAt3uhA"
				, "AKyu17SjcztoYXEUMGysK7z929afyhSADX"
				, "AKz19E6hF8fyiUiTtT6NiHu9k9y2abXPUq"
				, "AKz4WGwL1a7DwwDoRGti1GXyAiJADqbNfs"
				, "AKzDDE3w752mBEjpCPZtaGu7tGYa3vVuwS"
				, "AKzhsy9t8uLJK9cfVNmDHQ12jAkWCu6GGC"
				, "AKzjagJfxwJPcG9fKSDidu3iXPdYpeuyKP"
				, "AKznVWMRMfTTyxU3SjQYuHkRacGn32GcRU"
				, "AKzpuJ8QmypFFHsbxutC1rRtT9TR3BqvHK"
				, "AKZQ3ko7fogGB8PfF8zQDQx2L1YYrY9tpo"
				, "AKZSF8GtbTPJfKY7hKE83T1pNFYKsa38E2"
				, "AKzTFPLLxyMbsEsVbvX4gePm5v4CQxH2Mu"
				, "AKzWTtK4F6KrFaYudYjQpW1dP9zbuMwddj"
				, "AL1vLV4zRRxHxfB2JnfS8oy3rdcNTwpnMx"
				, "AL285C3uEp5GdW9jmZ92WuPeNTvE5FQrns"
				, "AL3KUmKLH4jPSrNpPfRBjLetomVxSTMLuY"
				, "AL3sXRNV1vuBr8AjoJkaMDfNiTykKfz6Gt"
				, "AL3wf6EeveE2cTFggs2gn2CVourYeQw5qs"
				, "AL42B4dvBi4xDbbbyxEBeVomiBRBXWyXYi"
				, "AL4AAHVWYNpuTygRzDbLPp2eTmeKcuKgi3"
				, "AL4Q3FpEzMKZFk9gaTtK6dyWfGQyzMLR6m"
				, "AL5aoXuM2CPJE3hFMtEKECELbmDg3nF1ou"
				, "AL5dYzWLccTCUB8GmLgbhKoFiiVp2Q55fs"
				, "AL5nyVzDWrfzPxHdeJmQUmF6BPb6jj8TuN"
				, "AL5SMsQE7FFKDz1PZsURrstzVrh3ErkdZk"
				, "AL5UqrfWXPtyKbzbYJ2cmnZxqt8vHmhDii"
				, "AL5ybMUkdkKpUHAKBt2bJFNPwSrKHNRXRL"
				, "AL5zQ8cSnESvvXV9XUVH8LYRedmX3bmGox"
				, "AL61zy4dDBLZ9R1Y2efEicSyL3Uea7HmNs"
				, "AL66GG5xjKYArVE2aA2AEgoNrJziqYmNbG"
				, "AL6WwJtuLbt9vP5z8FEPcBQYB1CCdE3Xe9"
				, "AL7SELVG4B7NtFVvsDbQ5mX8piUpV8rMbp"
				, "AL7VhWNVr8wnT1yk2onkRdvdLCUs4K4wCg"
				, "AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR"
				, "AL8NxSyfbyGBMnSytx2bAFSD4GjJp6hiAN"
				, "AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU"
				, "AL9chnA13Qu61HSesj9BTDokZVztDVkXpX"
				, "ALa5GHsmhHjUpMqftSua4xdAx9w9rqpNQ9"
				, "ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t"
				, "ALanXiNNT4My6BFQSw9NhvntfvwkAuUMpC"
				, "ALAUUDmB85wXBK6sQvPMtpzp765HbKCtUQ"
				, "ALB573j2FwvPYBW6kFRUkKk5yAqnoYVDtC"
				, "ALbBM6uv3xDBaxgcMLbVMJkgYtZnVbLBoJ"
				, "ALBMi5pfKXvT4wCS7Gw8y18Eqa8z4mfBsn"
				, "ALBNozsAUfrLMRJnYrtFpkCtbfZWuzsL4c"
				, "ALbSKYukTNY4PqoDz3CouxkhgfXYa4JHdd"
				, "ALbU6d847bRqpmnvrgxUL6UVLC6J1bNRT2"
				, "ALbYWCppeUMnMkSHc9ygZw8RiBN3Nuhvsg"
				, "ALcaexWgHGfi3Cv3eVHZEaWKP5yZLgv7e1"
				, "ALCpVkSeiMRfsFKnudgKwEJZZ7ETmJjCUk"
				, "ALCzkGfGY6dtezji2N5nAw4wmj8u5NzHAa"
				, "ALD5zvB34ttgRBpmfA3nMth1pjFwLugSsy"
				, "ALDkGzKKJVoGUWRLWndK212b4Tao9414oQ"
				, "ALdrhNtpgaARSMJ5FuKyEGKWuwyTcP5dqj"
				, "ALDvdokR1SrM41UccPfxcC7SiPG9ZmGYZr"
				, "ALE47gGnkLv1dZcEpQ8hWPpAoKmbZaLvFc"
				, "ALEdLhfhBHZn2Jwt9MStv1Y8RwYPSQi6TU"
				, "ALEgkQJ97C3rZg38sBdz78LWvyF43dJg6s"
				, "ALEMko1FgGWp7daoWPW7qh8DsyFueFkm5p"
				, "ALEqRK3Kj4fjxskvFbZCiWbbc1ChrxRJNA"
				, "ALeRwiFtmboReBftiugVsnsYbCBYCcQjVi"
				, "ALeS5xbX3jLi3QywJ2cKWMrGtnPdU8nCRF"
				, "ALEVFbUVyNw5scYhSrPha9Hxdo9U1t19tJ"
				, "ALf3V1XC9f7Twm871KY4pzTr5E4jYDFA41"
				, "ALFARuyZRPgWXYJCKSoNKfqNbu76eyufsm"
				, "ALfBSLLQXfq6m7N6rKEQHsVwfrpEUTket3"
				, "ALfEz15zzLzNY6RfiCoJx4vS2SpukpCdqo"
				, "ALfHWCXQ5hBiGfbXXkVXdeesjCar3Nesgo"
				, "ALfUGX4wahRg7xU8b3txpZkbtnX2YssU5k"
				, "ALFVdU1K8JzAcWSNNT7fFswSGwv5mHw8xu"
				, "ALFXGbAa3bnfYjDY4ZakkJVS2Q9xcqDYxw"
				, "ALGbT7UT4hssnhiPqZweoVXw4MAkTWEZJj"
				, "ALGC8LwtX8pgpSK5MMghP9ESowMuNk1xXK"
				, "ALGdVUj6BMeY9Fxzmoj6mc83nSdkbnVrMj"
				, "ALgvExuqK1vKNEiWizhpFWtZmTCEA5BviX"
				, "ALGVHqJj2ntRScujrtsup3rpSAfv6bwAX5"
				, "ALHbRhSqLkyZ4Xa9KXfzmPgBzhvNn1P7R8"
				, "ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa"
				, "ALHnYidaVqp5cvR8d3KKmduSkzapT5WNUc"
				, "ALHPRGs5u99gfUYtSSfQpfSzziPAucmu6U"
				, "ALHUMwQD3LMRVPn25mpKst8qQ5NtfnYqDv"
				, "ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU"
				, "ALi1umgaqVRvoCifik2vi4y86ghRkiDsVb"
				, "ALi8MbdG8zzpQavvV4SJWYHq9qxUCvcCV4"
				, "ALiRAwcUi1abKsWwfdgqYscZ9wSsC4bJJJ"
				, "ALiu67WTMs4DQoHu7ZZ8dDKN5CrhhSa3wr"
				, "ALjA57ZyReAmnUEpkrxW7a9vktC4NwTBZV"
				, "ALJAjfV3zBz4Nsr1KJJtegsP9MpD3p9z6J"
				, "ALJeDycypqd978dH5mu1oBWvkxT33ne79X"
				, "ALJtAVr6neXdswWBwuKz7QiyisBGC1ARn8"
				, "ALK3uptmDnj5jZ1xZMzKj2a3KCKpzG4Jy4"
				, "ALk8dWu4Gm557xwzCqgMoaycuSc4fSzP3a"
				, "ALKiSQ2Z7BzGdZAtx2TYY9iEKKp75fW5rx"
				, "ALkja9gngrNs2obk3bEju5a76nAxA1Q9XV"
				, "ALKmJHnDpNrKnv7z1YFm5YM3HCMER6saF3"
				, "ALkn6P535vHprZX3TRTHxGUdhPUdFQb4fv"
				, "ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV"
				, "ALKqHcqD7jZ59fec2pX5uJkc63gbu6WAgf"
				, "ALKuw8UApj8uFhZfugFwcih9AYLN7FUeAi"
				, "ALkxAMFGgU67SEahbT8Ds1eHTFeKWe7i6W"
				, "ALkzAwZUvX8jwtzGkEq4LRGdQUHbDLM4db"
				, "ALMD5MHVMcV2pD8kn1puA88BX8o1C8snsf"
				, "ALmGbLGiwXayS4afC9XketJVqcJ2Emdk1z"
				, "ALmjkPqpuuCGGVc9TcLzwfjGXpGMeVie2h"
				, "ALMm9kKCgz28AeWrkiJ1gBjwhxsVy91chi"
				, "ALmpLzA7Qnx4xfrUzSgG1PoFVXEnPgrRcD"
				, "ALMRibrCaNwRteUhG94roJPqRfvEWoJuBG"
				, "ALN9c9wd4Cv8ucnarwK6vSDr8t9YHGaiVs"
				, "ALnDQstmQc8rF8EhgxmEmrc9yuC4mHFW8S"
				, "ALnkhs2o6RqY3XyD75Z3RfNaexjnsR1zyk"
				, "ALnQTCx6kH2PJjSTi45jK33V4k9Tvb4iUT"
				, "ALNrEnz5o5Vh3ewK3ZNAZFosHLVENrTceY"
				, "ALnSVMifm5ZtdzxXdNhpkqrKkzkvZ5C8Rg"
				, "ALo8RSEfzMciiX9cdBerLXyF22wNsJxtao"
				, "ALoFdZShn84vwusprGhJx4Mw6spmU8Mi6Y"
				, "ALopqb9HBmQmv6b3vQxUdByjNV2FhhhqS5"
				, "ALp6yNAF3wu6ZzbEY9qfUJL77uc8ujgGr4"
				, "ALPTrhkfPUDFsJBmxHdnuirDkecYB7Hdxa"
				, "ALpzBSgDFKDnhX622VbiZaSP7GkjpsymyK"
				, "ALQdMrXrJX4ycoob7vxYkQBkv6DrXDkpCn"
				, "ALqgMRJDBnbSkai7bcfW6bxBTjYcA4HTpC"
				, "ALQJFecK6mDpYAvE3P7eCenDdtwNnb5eGm"
				, "ALQjqMbaLDSBYKY7oYC9JQ5jprSirXrpgH"
				, "ALQkn7gu3TMZC49az9BBToK62DKTyjdcvK"
				, "ALqRCWKiJ2Uo5mNXUKThSwRattjqfkc89E"
				, "ALr5KbquTgKBZnc6pXLaXcxeitFZcTBTbS"
				, "ALr7Ypj2TzTRaJiNtDhNvBCUTg5VFHy4v1"
				, "ALRfhdRmYeHmxcrXFbsPYkctKbbEpRHhvy"
				, "ALrhgf7UpaRWiLYsLCrZYUuBYRC4wqN6ov"
				, "ALrjeZpbWF1NCgCKMa8FHh6TV6k9GsyJmx"
				, "ALrmajDxDdvyRNA7Ru6W9nEic2f836RskB"
				, "ALrmidTWZgE6K7ur6tNpsiAUvQT1rn11WF"
				, "ALRWE76hmLo15UuckKUCuBz7Kw5LGpq8P6"
				, "ALRwnKS8aAbHebUJc4kigg3HFfuiADGhZK"
				, "ALrxfpafgUZ8cAZbMoBSWXs57hsJPWRRt7"
				, "ALs718WFtva9ifvgmCDrqztg7DpmTEp8YE"
				, "ALsAtKwxHwFkarR6nUXbU43LDxkGYk9UWx"
				, "ALSCMQ5HTF8qJczX2eZRSkVfGoFuHjwjm2"
				, "ALsG6hUKaAQfmXPLBxoDdRbJMdFd8vuYRi"
				, "ALsHqd2Th1w4djAGP3ZCos8BuZ8pVw3H6Y"
				, "ALsHRV9b9BDhiKKjMEpgFEpp1XuVjsL91Q"
				, "ALSJSt4kAhNoQKKVtsCZZdDRQb4kEuasVd"
				, "ALSrYFZ3aPr8gqHzP3xtKgevz32BtWsZQb"
				, "ALSS32CEbytDniModfX8JTu2TCoMkbhdoB"
				, "ALst4R8FnJdGhebDAa5wGBkaGic7CP7LsZ"
				, "ALSzGshJtKSZ9Z8CqthV9Jm11c5Xir9iRo"
				, "ALszn7ksRj1RgdtGexMZ6jz9YHHggcnMEV"
				, "ALTagR5v5MMmyRoFAEzNhsZBcQnQNjC2zd"
				, "ALTcu3zDsEXjMMgUwZycaoVRQRyXfpMtsW"
				, "ALtDydbmbiVxdtFXgKxMrp2jxLx3xQJyHU"
				, "ALTEwzv5hWjRfgh8uXzs1KizL72QQfHow7"
				, "ALtfNq6SVb9U3BjrSfkrQnHVfWgVofuhqQ"
				, "ALTHMFahstf1sFuhnN9HrMSWTGdfrxgrFd"
				, "ALTqTCYtZnYvVvzJE3Py3KGuxdrp8WPTKR"
				, "ALtvBn6GDAU3SMivqj5pBhwQYCypykeUDH"
				, "ALU3xvaNJxUX81chFvRKpaL2ysjjmsejw5"
				, "ALU7hs79AxvRzxpNmFQ2Q55J9LM8JbfMbC"
				, "ALuaUfPq7n1FSdbwPTvXGoQAtAj7v4eEf1"
				, "ALuAWRWYWRTVruzTLRFXR84CtKKxsEUSAK"
				, "ALUdbRDtK9NQkJAoA25poQfy1PtWYWG3km"
				, "ALUFASg8ZDvxuMPCMJHMd4tyTmvTNdvDtj"
				, "ALuTsyZWaGXZUJbxnLnGrKaEx4nwAJM1yn"
				, "ALv7WXc1D1cHADADVo74BqfN1H1UvuDPgj"
				, "ALviUto3qSKQaacAQh4M9uKuDYSYm4RBzU"
				, "ALvjX342BsW3AYkfR77rdK9cBU5boqtmrR"
				, "ALvprYadEjpVbNT8yqykRMqCyeGCo96nnp"
				, "ALwAKgGzqt3FpJPPmW1LDi6R9EtFAEetQr"
				, "ALwHrJmbrsbGfrLCwF6qhMonT3YP6n2MXZ"
				, "ALWiNa1AhwQCRdiKVBrgKoaDCw3X2qZ883"
				, "ALwjbqKJX89YmMBfUEnCr5n7qYYvBjFQnV"
				, "ALwJgUaonWDUoJf9Xos4JJN55sRs5iLVHn"
				, "ALWVwyYB28spNYecyXjD1QcfPjB1vzw9Y6"
				, "ALx2bmD5wmMo8kb6fn6AEAXEC715wnc6kq"
				, "ALx8AMQm38qU2B2UifxBL8Ae6LtZnzsK7Y"
				, "ALXdDahDBZu8J6NebiJC2aRehwtuY7ysCq"
				, "ALxqdBjDMp673X5dffDBgob5GRECkarqt7"
				, "ALXXQPPRBTjWBZZHKPsMRxUSUFUpDppuET"
				, "ALy2tmfbvf3uWFAGKxhndsoc2j9thivi2v"
				, "ALY76J129FsSr1mjne4BopeF7foos1be7e"
				, "ALym4vN4u1YsPbFDp9iwEoRS2cH44MY6hH"
				, "ALYofGRvjjBdBi9asVLormYQv9LtuDGWpn"
				, "ALyU2zK9FAw4C2mjZxGABWZiPCpGfeBEVd"
				, "ALZfBpGgHoBGScToHLiVRfLFs9iRwJrL2j"
				, "ALzfS2YKHybC27PQQVwqZsuhkcC9vPspUz"
				, "ALzJNFbfmxEEeoHwH3eDq3BkrPsdLHWk5w"
				, "ALZQ3pnQoXAHbzDTx9C9CYSk9Wx2M4e6hr"
				, "AM1CcngjSyM4bvV6D7enUmeFabpxobgTz6"
				, "AM1mbLJWtN4uSMmPQPiQ6X5WYxbgKmTh4k"
				, "AM1q89WapKng11PzsxdASKhETbp1MrFMPA"
				, "AM1s8cNqQV7s1c5SNgzsitYECJRc6aw43a"
				, "AM23sc2bbSybMRrnCM1EvbviSrijSRBzcp"
				, "AM2fJkgGyzm8K89sMYhDf5zgiXzYtNDv4v"
				, "AM2osMjMrxCQjHRhZtRAK2SSRSQuL367qJ"
				, "AM2zZrAkY9gN5Nz1SMShKdbQWDid7vRr9t"
				, "AM3PMssf2X25yK6dNcDHu5joNDyTR6euth"
				, "AM42mDVGRfWYi7oX1hGEWnNWXhXmpfTuBV"
				, "AM43uSthBkJQovveN6rP74eRCv6knbCbfQ"
				, "AM498LyZVFfMo3JaSWGvM5JR5FZevXKGoL"
				, "AM4geoWu5HihNxQ5Jauqz1Nf46utipsfTj"
				, "AM5CdzgHj1RFAyuymz1XdySgmXNCQToySS"
				, "AM5ftD6tKVrMPRz5ZEJJSCbuSGx4osWSes"
				, "AM5gcQtWpxNADcNCzEouNuk8LsGepwnRNC"
				, "AM5nKPQRFC94Khr5P5sFfTbWREuuqNFLdG"
				, "AM5wsMYk7jn2beZSc1VmTDHrdDPPd2JG7w"
				, "AM6k1EksQWn8QxvMakQs3pUk5eGXEMjbg2"
				, "AM6S9iiKRe9dMvD1GLWYDLXfgUmvy73hVz"
				, "AM6v4BuhsKp6vHbnc8wsPFXKJP67AFLt1s"
				, "AM7N4GYZJdF438xWMxF98Jztt9rLkEodrM"
				, "AM7ZhyjoVMHNzcFATXA1V5PSGMRabgnY7F"
				, "AM8TfcTxFFRAFBauYBNZtbCBY5bzhKxoPe"
				, "AM8wogCr8i7gmiEHxW1jKYXtki8gNFPZBb"
				, "AM8Z9t9zLvPy5ii5QgWetNnnL5oeLGmJAi"
				, "AM9pSChvtNHRqL7ZFCiLDZZFLbvNBagSNA"
				, "AMa2xibZzXEXsHs12xxuKaHxdxG1QuUt6b"
				, "AMAaaoyNDqwiwU4U5PtmFx5BgWUyD1fJaS"
				, "AMAooZFPCQyFcGpDNwrfVuxVtBtRmC3ow5"
				, "AMb77MfZxpuWtfAPjSvkfyQiRjGEPz8Nwe"
				, "AMbGKK9zA4747fRQuKsJPu7eHoGh68gB1T"
				, "AMboqmhc8xKgrxdPEq65BoYxB53n4rx4pR"
				, "AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe"
				, "AMc7DPComCbA6q7DRE3hbVFTWQnoHFvPAh"
				, "AMcbUeV4uTQgpLkfkePT2CjWBKDpJA6pW2"
				, "AMcRVq6ade9jL3FPBnJM3Jj26bK4BUHNLD"
				, "AMcZ4DFEb2ijNHaAV9RcSz6jWhsgo29aJP"
				, "AMd6doUSh64BEWTDVFu8dMB8xJLcocdbqF"
				, "AMDHwt1oQQVrghy9qb5EnULNug5dKH5LnR"
				, "AMe5PCS36N9guq1U13J9Y9VtVxewtjJTwb"
				, "AMEkktBx8VMLgF7HZGCBqaSSnK7PV2j2kN"
				, "AMEkytHqwPF4SLxrefi57teVrmEmxGNZ1f"
				, "AMELZ17eQ4CMzdLAe3fib5wTDCvG1c7QQk"
				, "AMeMwjiVKTmH6sWAcBfYSjJ7nfKM3yNUD2"
				, "AMeZg4rsmqT7M9Hzf8PRTWyAuBFpaooTW3"
				, "AMFbKZVio92oRu8C6zPye8f9thFcuyjxys"
				, "AMfhNAuJYFBChBk6F2SbjBTWpSFAzx4Y8V"
				, "AMFqPQhrGWGpV4cMGD8Ui11DEPdZzCp2Sn"
				, "AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC"
				, "AMGdtRRSm1fngmJrqmQRSEm6Fk9kirgkUq"
				, "AMgNMcikSAacHN4pkthqRnLSMjJfwV3c7d"
				, "AMGQQGpyUrQde7bqGrfz5wLPscUJQ7arvR"
				, "AMhdsE3gTLN9jdTY9ikNxqriDYNbG78P3j"
				, "AMhnLLVhkGUxFBy1J4cntsoyWxQsAFcuoq"
				, "AMHum13CHPaGEHczfV76Y1qbqC5Eys4mna"
				, "AMhuunvDhsvzosHFywnHuzrHiS1Cnu1xhY"
				, "AMHwqYbM4CVuxAQ7cdZ6oSMjHpdaChQsf2"
				, "AMigesggpWgRjYBzb55g5yptX9bzYWc4Hx"
				, "AMiNWge3gCmxjGZnA2TdhLLgLdxreq1YnY"
				, "AMJdKTBimGA9jL5rVXwvmYuGah72ZkHkRH"
				, "AMJE7XSEGxh5L8oZDKeUF5Mt8VWiKtMFzf"
				, "AMJfDCfyiRrsymqGPgZGzcK2jBoSfCEKC4"
				, "AMJgE7PE4XXG7UJvhnaBeTg7PeeUvnAoq3"
				, "AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv"
				, "AMjTtXhWDc1PM1jLutiw3SyGWEa58npLos"
				, "AMjYTCqCwMfByH6XZ6FoEi1GHHkTqUm3s8"
				, "AMK91GVDYESQNNH7L3JjJ1GoaAoCNuRV6R"
				, "AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut"
				, "AMKhiFwecqrUdxKrPGU5REsnBXZKYCLgZD"
				, "AMKhpL8hU5nqdL79SFDTiSELSSJzVcCiCM"
				, "AMkmppkBcCyVTfDTg8Y35o5dpQ1LHs8pdw"
				, "AMkPBGBJvoAmcFvhCAtUYd25XxJXSYJRjB"
				, "AMKutECDSXVK8oJFQptbnZsoQLnEyZEbus"
				, "AML8ySZss7igpjh7CKqzni6ZUgEnswuKDC"
				, "AMLcUzkvEMpr9E7UAiQifBs7M4w62vM4Qi"
				, "AMLs7NzPPrcLvDW95zseAXLNkLhmFrBxSm"
				, "AMLz3e17jRm44bGYtpr8NgbdyWSLygZ5L2"
				, "AMmCT5wx2DugpSSsdtfSmwKTo4zX8B9eyy"
				, "AMMfhfegNgzvg5qBn22xquwad5Ah6hHK6w"
				, "AMMfiJnv2L4FY3H4ASKeA2cuGoKm9zLEoE"
				, "AMMmApZh3wMu7kogDnmBubZ1ZS85sLC4P2"
				, "AMMNT5hY2LTkYCwaFeYWrSoYFKhXp3G8Sf"
				, "AMmosUKqfMYJwwQ5MfFiXjBF1kPNxPRvGd"
				, "AMmqkzQyZNnUamdgTVkoNCbAPHyKip5oyX"
				, "AMn1drrjAdLQbGHrGkEZ4SnTkFYroLwdhQ"
				, "AMn2sZqNGxEw9eGhsUhWRB51XGxjuXUNG5"
				, "AMN5MBgyafCjS9AvMFeJ5yCrhgjB511MfL"
				, "AMnbeZ6teuxNDphw1PCtAfFF6LoxTv1oGd"
				, "AMNiiLwp7PWDbxHtVgmHME8ZuFdGS9vd9k"
				, "AMnP8mW4bdhi2B6B1A2idbgZW4nPAdJ5s8"
				, "AMnxE6qnYB5PWXhLgu6eV6egf1VCgcXrj9"
				, "AMoVYpdd3nic3WoELsnVHqExPBfkKEeRcP"
				, "AMP8wbwsypHXS52f9kcAfhVYVogJWzFU5x"
				, "AMPbcsqHcEdH2L3dUMg3xbnoQEnar44SkV"
				, "AMpCf8wQPD2vxZRzCiBdu8yJu4L4FQGbST"
				, "AMpe9NHutxa2YRWEfWxhKcMAmQhEs7kKsA"
				, "AMPffqwyz4oGbndfaBo3wDnkbZF1mP9VuV"
				, "AMpifyrrp1UP9v2g6unjmcWXKZ6xQh4qYV"
				, "AMPqY96LGq42ad2HvfiJnKNpLY1HeeFJYf"
				, "AMprZNoyVLqeAv9HpNgpFpS51xn8i981M6"
				, "AMPTXxGLYnmwF4TiKqJTjiVRN1J9UBqcrW"
				, "AMq8mK3Eg22FPuWJYf6tkPYdfPnP93yTDn"
				, "AMQngdDyz1HM25Smg2rFrJhY23WUPxoTci"
				, "AMqwvDbK95Dyhvf7uvCcxJQdyWsYLAcaST"
				, "AMqykXvYjBsgjoMpTYAhGzZ9ks2otciCYY"
				, "AMRbwWGAeB7jTXWZkPZRwoUZjijiig3DMc"
				, "AMRFHtiiSefvPQAiWvpZLxqSwtwZkahn1n"
				, "AMRMu55qCT4AaLvnJ3zZ2UkorRfpWBCgQ9"
				, "AMrsTM3KPrG3dmTuzKxqTZaYrhC1AGWk5z"
				, "AMrTPP6uWuW9mwwd6LTqQTaZNqQGQVbBYo"
				, "AMRVxScXVcCZb3E1uUPU1STKFwxrT9YXu7"
				, "AMRxSSGg1P1MXacfbChNFAwSFPgnEGhQSN"
				, "AMSCoLGkfJHiFjtXci7iVSx27QpCzXfj62"
				, "AMSo2MFTeEpQDefWHUTSm3KQu6gvdBbqcc"
				, "AMSR27X4i4DPgubi1XxWEvXZpahJnjV29d"
				, "AMsSoZocM7z3jjUHftXAk9XFna9E1oiEna"
				, "AMsu6J6gMZ1Q18aFhcprao4PJ9JJ7dDfvk"
				, "AMsyXkeN8UJv8EfSoGUgs1XUx4597ZNXLc"
				, "AMtksKPqpGyBcrffUUNCESKEBWwkKM44GN"
				, "AMtmWLo1wMkbDZWUf9UFV4fBWUJC9XnVsm"
				, "AMTwMsKWpAnyVCYTxQmY4oTpjD1G2NYTGY"
				, "AMTYUF1Gv7hTtLSTjNeBMmaegZLdXmVtbB"
				, "AMTzBr9Ky5zePzrRUuzoYfNewwGrewYGep"
				, "AMu9r6cgMDApZjyYuwiMpN7SA5N8jBNnQ8"
				, "AMu9XADnk9Pb9bYQtLNRvwYkviPkkcCn6b"
				, "AMUe5QxouKLT2BYarawmA1bzsaQ5xWBrw8"
				, "AMUi4By63kWzWx1XMQbWt2EquACQf3cbRF"
				, "AMuoiwC5kizU25RPx8zY4AZBkiQwrMaV8N"
				, "AMV8cccMjzyTEFAWoRHys6jCzbg8bVNoyu"
				, "AMV9q54ffTR4oW8EN4J57XWsGX3wpf67eg"
				, "AMvjZ5KiyUXadnsPv251XSpJ3DQQj35WrP"
				, "AMvwUKkZug6HotZutx9GDSCaHYxy4NpThY"
				, "AMW4RdjJAswpmN6EWRkWoB9JXDpZ6We9Q1"
				, "AMw8LhKiNX7WDF7hxkXRRf3Qi4moCb4HhC"
				, "AMwCZjXTLm5gNYirhRqLojeSmyG1W6Sv3G"
				, "AMwkWVKWxF22rcWTFHfELm5yAnKrRKvJWN"
				, "AMWM2PdjVrkZEkXQPwvR8rRB1YBLKNtis9"
				, "AMWRMBzRpyhNZQvCsbDJJ61UwCwiSw8vgX"
				, "AMWUigdtXCvgMVPyuhNoV8D7eQhZTiAg1E"
				, "AMwv9Mz1Mh6Az4yRGYyCSm9quCbfQ45FoB"
				, "AMWxg1sB5w4bQJQppiLdtqYXmaDSBpypqM"
				, "AMWXN4mz5YvWpKdDWvoocaoiH5yKKsiysb"
				, "AMWyd6vyA4f5vZVva2HHQbK4S2wdxVMuun"
				, "AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm"
				, "AMxmjErxufbbdKjnfjJrojhpaeVjUR6S9G"
				, "AMXsoyV5Bwkwy2j94fBsmyvJSrZKvceuyg"
				, "AMXvFpYsBxuDGpSFgcJCzxcFuUBuraxNvi"
				, "AMy9yJyC7EuPfeR6LjzRFdgmeKMSLmV3ze"
				, "AMYbEAVXtZ17ksMyxsaBjfJTgsXdH2g3r4"
				, "AMybWooET5Kv71MuiAB9wFmDVFdjEDW55i"
				, "AMYDPweRLSRhwbBgnxWbJ5aoKoFC5Kkaz2"
				, "AMYhKAVUNxnxQ64NqUKU4bpS9pxyU8UJeV"
				, "AMYtMqX3Nz1QkigmFRUm5HZ8ciUTGyh7iz"
				, "AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj"
				, "AMYwriwHp9BFCJuGDCrNwYBA2JbRrXNCeV"
				, "AMyxyPEqNapwV4Q91XP8n7egYsijueZmcV"
				, "AMYyKVFDa5Kz9AQ8bVT4ZyfeGVRwT5HDPG"
				, "AMz3RoiGivKqq2s4KF5hBttnQTR3cyJ8eR"
				, "AMZ6ap8mqDbWniNAfSeWEwnZu7r2hnw6m6"
				, "AMzBuQKuaVX3smPYLfWRu3gXX6mzRoqV41"
				, "AMzCnmy4qgDfmcM2zCxQ4SHcxarN4hcu4S"
				, "AMZcp8nH69h21St7pXaKVtPvcape6pc5ZD"
				, "AMZE7zNME2HmV2HZxoeMSDfnCXeXqKTNtR"
				, "AMzMAUZkC1buoUUwGmutcxgPvzcWsQhRQP"
				, "AMZNfaRnr3s5E48wtHFC5ZpEJ9FMajVsHA"
				, "AMzp7mQc3TSNroVga6ej26LmkoS6bdS85x"
				, "AMzq5A66jU9ZpxTAH55wfqdvxMUaspwk8e"
				, "AMzvqXNUKCwoD7aY9RGYWXkuMDSxYknkwu"
				, "AMzZyFDE2SRpiXaund4ibJZBryhZMZAdZY"
				, "AN14N1SipUMgxVJyYif57VAuce8yTk7Jxy"
				, "AN1FpXcRAUBpAMgzmGLSTzcCWqkWeR4xuh"
				, "AN2G1dEUv13WxmnDWW94nsEfgMmhjatuAP"
				, "AN2VUBDYuNru6b3giKa66p9kEebaF5PnCV"
				, "AN34WVeLdij87FXaFLU1oL9fkK3GfMAQFU"
				, "AN35tn5L8pXb86DnBxWe6vQkTMnEiM3Rbk"
				, "AN41p3rz6rdx9qDjbgvYAdufFwXyoHUpFK"
				, "AN4R56i4naZHY3oNrGrbJGSrpC62CFRNqK"
				, "AN56LG3sPMVK8deAo184SrRMq8RKRayRfn"
				, "AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV"
				, "AN5ufEKAjSx4DRpV6suWR8YQS9ZekU7gan"
				, "AN5vg64xpshDjiwa1aJwNPzCFR17KtGEhQ"
				, "AN5vY5uWSudvpT8yDpSxxm7GewFK1gXKQB"
				, "AN6bvgTS92KPu8xhdEkkCutzGe5PqZxQEJ"
				, "AN73K1JV7tcNummcya9TYWWzTkL6PCrQHv"
				, "AN77uNVBvBxnpGQp3kWXP2XFBqfj6bCEVN"
				, "AN88EtJCq7zbyNz9ifbLRWyUnGcb992YTY"
				, "AN8gzBWbGbu7jVgQuW8jhq2xwWEgc8DTbB"
				, "AN9Ax7UPh9DnnH4ffTQcMq6CgVTrYjfaMT"
				, "AN9g5RR6bHZDgDQEHFc3sG6BucYUXgWGrf"
				, "AN9NPczXJmiB91YtsupSswmnt8RjEBkUcq"
				, "ANAHpEeRQD2RqhTkMPTi6SebZeMwnyLy5i"
				, "ANakyPu1nTHE3XYSXQKwFsR2pVyDZctkiB"
				, "ANan54bohWz4obpz5qzJwWXxUiPhHdHrLP"
				, "ANanTkhbTLfYhn7quise9JkHKXmpD2HnNT"
				, "ANao9kgAx4f1ZfbJ814kt6RYtp3dthY5Gg"
				, "ANaSZ9x9fRVx8p32ACa8CwWEWce6CiGSRE"
				, "ANAuebkCj3zjvCQw94RRay9CznbuL5tSgr"
				, "ANbGyQo9siR135bUZiAbzP9uFsCYvUSAog"
				, "ANbv7dYTJW85EgdeAVHT5H5mxs9WWyYsXx"
				, "ANbxDfjfZEvGUfmjRMi5kKGHdAYuWi3s88"
				, "ANbXDSJHhud7wptvFRF9a2vvm9Bzc2W3uT"
				, "ANC3xyS1zPcBFuDyRZVhmjPmUGVN3VbrKZ"
				, "ANC9RKPhRi3QYkE51pbRD165Zq9oCZjaws"
				, "ANcDAU2mpA5uYppZuDYnU4yZiATauZdAzR"
				, "ANcmLfeDjoBc5ZUBLNQSN7sWguKCwYmDKX"
				, "ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7"
				, "ANcRdistzLY2LMDrFYvXsLzR4nef6C6HsN"
				, "ANCUZSSS5KPTtpPrUJ68NDX51YUD6mQ8Cq"
				, "ANCYVzQAXfJzf2FBB4Ngb7VRNfXAPCP17P"
				, "ANDAXJrwP3fq1HkvLx8tkbTRZMmFX83vTx"
				, "ANdevAoRFicPPL65mWG5fyU8dkDim74NGk"
				, "ANdVJAQUmQzQaU5KnGUmX1FsB87XbHAUau"
				, "ANe34AZUDtk14qHq4Jq6LE6CPw7rLT5YHE"
				, "ANE4x1zT5KVfbgpuioT56oTkt4WJ8bJkWM"
				, "ANEe55MscasjzPAQNWgQ2jBgrgTT7HdFHB"
				, "ANEEvzvC8vtuhDkZPKsxs9gzhQvtVphpGK"
				, "ANEitRfgxaTxGXXbFBUUMxkgyV68xqLwpx"
				, "ANepr4F4TsSDRng9mv6jBjcfCx54vQ5YQs"
				, "ANeRhhWdSZkFRT8pmQ5mYrD9mMtEtypHN7"
				, "ANesvSDq9LrsqEr3mGoMdJLPsD68RmXHFB"
				, "ANFNiXZ1eYEw2kmDXgezQzSmDfE9W6y2v2"
				, "ANfPLHvQWgKAEvUgJc7fsEr3fYMnydWbi2"
				, "ANFuaCb1dnfNCSgae8TcP4nhGFB8ZtUBKP"
				, "ANFuSUBUDPckQpzujmqRqrcnVbUujv24UD"
				, "ANFxM23Navv1j7fqpaJcAR5Rt7ua9hrnzA"
				, "ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD"
				, "ANFzFqxmWKDHo81eEYfrvnhfQ8tTGEWssq"
				, "ANg1bYGtntSxAec5x9yTtq9rzfTWLxQBDv"
				, "ANGkMBEDfpuojSBmeANurfr2HWnkCgghE1"
				, "ANgL8gw1bBfyGTxoS8HUQzLnmqWovLeKku"
				, "ANgmHsn4ENLqFxQx2ztmGMkwTTajMbSZmX"
				, "ANGnkqAVCGEm5pvbDv5Pe3Vh6sD57xjcbi"
				, "ANGtWHuyfiix5ae9gVmdkmG86hUEUTbwkY"
				, "ANGZy7rDPVd9pirmnNsVoqGSFT4hpCFupb"
				, "ANhdaMxhaxaLfbuLdnHTCYb58g4uXqDAxs"
				, "ANhEggtg6jfwmTC4NjFvJqc99nnP6JUZbw"
				, "ANheRJVnE6hnj5gAmongqQYiTp24jpcscT"
				, "ANHFJgLsi6P4Ssm6JvTSd8gUFUvW8o5hyE"
				, "ANhggDjdBFPR9yTnLdZgJoGWMgy4WFpdN3"
				, "ANHoQaP2bjzwmHb8jN3Rp5thG4hQVCWFta"
				, "ANHpobP3aRJXhJ7yMDxqWF7Fzj9C7e4Nad"
				, "ANhSEhXAJrBmDeVeFuRtDwE1XfJbhXNFg3"
				, "ANiHVXxdSnJftVoqPmuXz65MGVSdgyKs1B"
				, "ANiMyc8Pdz7D6pCx6vaTVt9QbWZTEaJ3Mk"
				, "ANj8TPFinm8RFTffUZz1DTjRMJ8jav3oW6"
				, "ANJFqxQ83ispTnFQ7MmGaXGEceCevnVH1x"
				, "ANjG7znUa4kbGvh7th7kwrsvF48tGYoXvy"
				, "ANjUsTb1BRdKMvBg5qLHzyK4nbjrT8jEXs"
				, "ANjUZYMgigtRDpTwSHmXvdFAGaM4oYeph1"
				, "ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF"
				, "ANJzgSvm2FNY8ajjeW4sRD3rmZMfFBW5oM"
				, "ANK4qEMwsHvJ5WRbhw2X9uBqrxU9E11RSA"
				, "ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1"
				, "ANKMUpAZge8EmyjMJGeFgeBP6JNXpacZ4W"
				, "ANKQpvimZ46VWjCLbQwGKxh9VSQXqytGmS"
				, "ANKSb9e4fGGLbttGAxa7UGAc7awTivCbGk"
				, "ANkWAtw3u6HZCQmUXekPZLXxwG63Lc2iw7"
				, "ANL3jRsczx32fYMA6eFqhkw4F51N6rbriQ"
				, "ANL9Pwz4hkmUyJJES1QyCkZT2vk5DRJYA4"
				, "ANLCXuyqC4aUvaRk6RAe34tWQ9zzBsptEE"
				, "ANLe1U6N8yBCAEfkigzDUfub3DNtq41dhj"
				, "ANM5qo2Nb4sBknBYEs28JZyc1XsqfNNxtR"
				, "ANm8xqJcPepSuN5yGiNd9rrHyARFWTjhFZ"
				, "ANM8xSPi4Hndi6e7HpxbjYfCStbReu7SX4"
				, "ANM91MFBT2onoz1RJAgGHkUQ7EtyZmhy4x"
				, "ANMevQSapD7EDQGNULUE3KnpED5guGbgWh"
				, "ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs"
				, "ANMJeVoH4kvrLpwNKZkm4fRZNtNTyDhejd"
				, "ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC"
				, "ANmqFrrFZFMLsURwRXwCnxeQYvbam8tBmL"
				, "ANMRDP7niamoLjAVWhssMWzFLtHVoHynpR"
				, "ANmu19gqtTEpsA19VT2nENaryy56cushrB"
				, "ANmvcrcrPfo8jSoBBqvK4D8BkMYwhkrdB5"
				, "ANMxm5hGSyCZN2k2sG5fs75pFggbuKEzny"
				, "ANn7J6K7PMajyt9cEAixkHwq4qr21cWyGL"
				, "ANnwU4Spgv57VAVpiBzpEHJJCAARBjSvko"
				, "ANoqKXSeJcuHcuHW961v2XU2xSt15E7JQL"
				, "ANpah5jPNpG4YFk4CRgaq4p96io9Fu93x2"
				, "ANPBuhfqRDrEP4VeCdMTawVThmBpLrEdMH"
				, "ANpXFb1sVeTNjKfK42Mys3hEaTshVeWgjH"
				, "ANQdsaCUyy4NLJAtyrLUwcz29vXQggYLQH"
				, "ANQEJLp5tqr7V5ygcgHJkAaDB2m3AsJpnF"
				, "ANQFpupJW7MDFMP9k6am8vBJxWQJDndmFe"
				, "ANqvCq5HcDBiuGXujUM2d3GBqPYDnQsuQV"
				, "ANqvk9Z6q8okzBo93TkPyweQJvpRycJiKr"
				, "ANR5EjM9nXq2DXc6WaXNEN2GRAzwCufn7t"
				, "ANrknTfYK16NMo7ZNBm44iqKDEwoUoG1Fh"
				, "ANrpk2ETt2fL5iqt6gn1U5Wk6dBiPHnQFD"
				, "ANrpkxaDzMiSnZp2rSmtuV9jJs2NsZ3m1t"
				, "ANSbZJBgrikCrYy6PSNAVV4tGgwFVG1zYn"
				, "ANsnQsrS13eN13nGGTmkdqmPocwajG3yBr"
				, "ANSPeGf6dUJZw6YxXkDEhudcoh4nc5Vhzo"
				, "ANtfBMLXQZGqwBHHAWsP5cozqy7UZp56Y1"
				, "ANtHp49LP6EABcDN9kvzKpjosPdkG2FYJj"
				, "ANtjyqihhybfBeUvuFQ1BtjQbbKQH3WcCc"
				, "ANTPJkj6Aa1dX4pkNpbbNjU6xJcmqTjnYa"
				, "ANtZ227r2YssMxgqLN8B1vppgxVxhc6ECi"
				, "ANtZ8Pqy4Usa1bnf4njXaRPp5ej4XMWGMH"
				, "ANUBMzdukQCAX7sVJfDfyLs2cHc617TiQu"
				, "ANUhwfk22Z8cScsM29xtZZiqokAdZ1HF8j"
				, "ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR"
				, "ANuMLpf4GZuDEypKAeJN7DbQWWvQz6ewEb"
				, "ANUNtY7eA5apsC6CdZZehzYnyKdefC1DLi"
				, "ANuPZZA64D3gbuf66KxvYGXfd95BX6Ffzy"
				, "ANUX4KUEYh2qH9GK7g6n2r2DxcFYK16Grf"
				, "ANuZChWWAWKbZ4ket7ME7QJEBebrCCUF2N"
				, "ANv9qq27isya9Eoo6aUrr25YRA1XUJdgQ8"
				, "ANVA1xKLAGDnVQKNNNGnyy4K8dqy8TJzDb"
				, "ANVAyZdFyFbG7kzSoXDrHWsZFc86k2tFbz"
				, "ANVBk4MzhkaHSAz9u6urxUFDpFjCbSK88v"
				, "ANVdbipA3wjhjVRHGof6227LrdFXjhzRCT"
				, "ANvMwxNPADYrJ69tBdhhqQC8WrHX5REiyk"
				, "ANvqiYQnaRm57WHBy5rLNA1gmDaf8TwuF5"
				, "ANVRGhU3uAJWfVDs5NyxdWxY3ruZnD5q9t"
				, "ANvtBVGioo8Kow4nfnwSgpV1qkKroZSUYS"
				, "ANvtK9dtENwJLWuQB45amddtrYncBpFbbg"
				, "ANVYFkUEyfVQyCuwrENFYwvv4xobujs1qi"
				, "ANVyYgN9TFfAivMwXLjPL54oUBageHAiXn"
				, "ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F"
				, "ANW9g73eemaMXXorsjBkUTPZtJE4YizupT"
				, "ANwfHzWuY6KW9eyPC66o3GiesxevD7SB3T"
				, "ANWQJUX66nb33LofGKzEAQ74krjP4xKNcK"
				, "ANwRGTrY1ebo5pbz6GKoAqW8GyMkDy3tyA"
				, "ANwWQ6CCGDL7whXLCoeiwDycKQC2Tmf4aw"
				, "ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws"
				, "ANxvEzbKsEo1UA5nWafs7yKWbeEuDRHLTM"
				, "ANXWberAit9Xcp5yYqCgb642dmgMySBp1m"
				, "ANxyLLGpRN4U6uMC8S7z48mV5n5m8jLiSW"
				, "ANy2iqqRsWuoS7DcySxzUF8h9e8Wjod4tY"
				, "ANy9r74273YgPza9fay1pFFQgVRnhq6PkP"
				, "ANyC2LCWk1CNYRkBgNFX2hejYJn1ywijES"
				, "ANyFgMguqyFMbqWj3Gih8XdLsfTwhMGP1e"
				, "ANYGSZH6WMBgpBf2NkWMhH9wqMRvoqmEhH"
				, "ANyJt7mNDfeNifa6woXguk8oxxX8ydo4v5"
				, "ANyq3hgxrhnUgXFRkioXuHpMDzaU2qhugg"
				, "ANyQ8XG9BdfbHJfRLuSZys8Fr6vqTyDD6L"
				, "ANZqNVDCwF2Wy1D1qmkgeQHKL97QMzpUXv"
				, "ANzqwqvu7LXAHGCFweLrFxqqYFNA6FMbpa"
				, "ANZTQGNPctw4vazQHpXrUmBiDmJYdxEGfg"
				, "ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J"
				, "AP11QBfZ4hUrTHURvyTCXNtehqimGjrTyY"
				, "AP12RVwQmJ1SUNyUvttBdrkdbzyFTCpNbw"
				, "AP26h9bkkckkmC8fac8ooRgmBEHdmf69nh"
				, "AP29ZvBZPpvASzPkKq5EzaMRP33PSXb2AN"
				, "AP2ceLEb9gANBoHFWzKsskbtiLEecxC9jN"
				, "AP2cuuBqadV69A96Xo31ktn3mqZjm6pizt"
				, "AP2PzqEUuyhtsCdpAQERiWs26AAExDc97v"
				, "AP2TCmERybjvr6RiN4Ygfc3NXn66Rz4E2S"
				, "AP2TFhgqh7WfN4Du8hNFPrSi9PKirHQRPy"
				, "AP2vtTg7JTvgfZvm15GYKGuthXHZWtZT4H"
				, "AP39Z3yTtbT2EVMfGQKps9Es9un6x6T6Gd"
				, "AP3QUGTLEVAVtfqbKq4WTaFhiLwtDiaGXi"
				, "AP4AG5hiDLxt2sFSwy2X2K2LBavdj3fPrj"
				, "AP4ds7FHHWJLQpZbYydZa9keYnZaP8UtpH"
				, "AP4fk3VRAmSGX75XRpW2hmaN3nVLo9f3kZ"
				, "AP4S4tr2x6rAqxEmGcTqtC1KqjnzQM8589"
				, "AP4wi1X5HnpqBrAfK9wu2N9Vvb5xuwDApe"
				, "AP5HL4jJ52ZFop8kezN1VJBT7xjKWVg791"
				, "AP5tdEdJtZBN6edo3hTKN5HWE1QVjbHwWn"
				, "AP5wSyyR91gWdpxTW8mG22hxStDJhCNYL3"
				, "AP6AMd5Gh7DZJsuGGCBiPpQhF4KPVbJhbP"
				, "AP6MZ6cKognPQzw69BmZ6eo9kUBszcUUFf"
				, "AP6quCLz1xaeYeH1puYPuBVi6Xh2i4DcLR"
				, "AP7BFjVgSLQ9mLvAe91E5PrG9th5QAPj34"
				, "AP7gAcs6A2sSiF5dCbJKsJApBt38GMYkEW"
				, "AP7ooPyBs7y89jTuXzeemBDjmvpxg6v6iw"
				, "AP7QE9DGRks1nMWWevZLSb7Nj4sFQi4H2v"
				, "AP898TPj1jS3SPCnYL2LagmuBwpdJLWfRJ"
				, "AP9b5c3kN61Sy2efvXVwE4VDLXotqz9cgC"
				, "AP9DDgaubP6yoPXGr1yjzB3b8qcsh3np4N"
				, "AP9oniCSxMDwEb8jyBa3QiJUPMQYDcTRiF"
				, "AP9sYMBkLMQ2VdFCUJuq3J8jntS1UpyPaV"
				, "AP9V1ine476XTmKt6wLfeyxfCwhh9g88v2"
				, "APaAEYAtMrmgSHUAg7p2RE2eHRopM1u6fJ"
				, "APAEAnfNZK42DFpK7iVGjGq88qFrGoSqyQ"
				, "APafLhv21sLnmZyfR2eZ2CLZKKYwr7XbJe"
				, "APAJ8TwU1dvyW9uvZ3xzxYe9CPhK6UEf3Y"
				, "APAPv7sH5YD6LpJtwh5fuWhonwcCKbvmtD"
				, "APat8ccBaVEYL8JBeM3PAX7jAhVjrNXU8X"
				, "APb12AQeJGnCZb3NVoyUirodKSu4MeyNoF"
				, "APBBjUffnHhamr14JQ9LjuJ2QYPokYrBD4"
				, "APBDJjfxYAysxoGHsrCWga8uVtWnQoHwhj"
				, "APbSwZjZb8DodyJRsXetgEybZBWzwYUWZc"
				, "APbUetnvbChZFZA9Sax1J32pWA9DRJzFPB"
				, "APbwyPc5kbawdqNm95cFDLKdRrtUVuMfQA"
				, "APc1PCY5C85adne9zxVdUihDy2ZKzqvdDD"
				, "APcCXHNpjLqfRa9AFy9pv2H5f76TZR69mB"
				, "APcDXNnrc5gL1o1x7Px3z56KTZmGky7gCz"
				, "APCgeajTakKvMHC1vNH6E4CEqSWtPQGm8g"
				, "APCKYpXy5UhPwm4athn1AmCtwRszBpnE3w"
				, "APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3"
				, "APDGHM8oBrq5ZarNa629GLbBuxGjNK3sdu"
				, "APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku"
				, "APdPq3BGJ9aQ7brPDvt5a6cJsmNCfWK9Sr"
				, "APDsiXowp37UhvzmsKAQFD1RZeWdE9HXqi"
				, "APdx4gwJ1S6DYNgPkvcCQjYVFsbHC3tzgC"
				, "APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63"
				, "APEEnwK7r3F7tm7RcqHrxvbAMbsAVfM6Af"
				, "APerTUZdteX1Deankbz4EyswTHLf5iU9AH"
				, "APeSFf9FHsNERTzFvubDggHz7asXDn1kR1"
				, "APEtnNYzK31HVSzL6Y4wedz9vTh79mbgHS"
				, "APexUYQQ2ir1k5XgeHctfv5dGWyudmZvXT"
				, "APeztUkJJiwpXxMgxD7Uk87LCxPJPtNyyi"
				, "APF1TW6fy73Tgbcck6bcjV6M7DaruGADSx"
				, "APf7VnjdbccEyH1xQcLWVf8U79o7My6oV2"
				, "APFdaGvQhHX8jLJs9BkcamMUHVfDAHMJp1"
				, "APfhzihRU6xfBazQZuqSTFRP9QPDqDbPah"
				, "APFxmaiKwLsw2r7mjMg5st7tRoW4Sf5E6t"
				, "APGMcUJ4ZDfK349JqDT8iq2fgYd4AZu91o"
				, "APGPnH2KBw8ws7YxdqgrGjAZ8vQYi5ym6S"
				, "APGuCmF6KjqL3NMzBWVUG5LacP7JroHMaM"
				, "APgVPVmydL3LkxF6tmXkBqLtrqepeBXdAQ"
				, "APGvR8VmnjFMcoBifjvGuopUYpGsfh7RUa"
				, "APGXbEFTs82T7rmYs8UFzTHWZoTzfunvU2"
				, "APGxN9Txm8v7XmzQ21NhJ7kyvB4NTqKZAg"
				, "APgYjEQUSSF8CHgarvu4p6ND5uwkT7Rxqx"
				, "APH7xTypTRGASrw7uwfMeBE3oLc9nK2gYZ"
				, "APhddGDBaARk22KygBz14Q4yef11PvPrUU"
				, "APhf8NALd7CHC1Lgo8eTchGGDzdHpwGwK4"
				, "APHJb7M2yoywyEUybBqiR1FV3YNDj9iQQF"
				, "APHLypPcaZ3RAFEEU7F5hr52Z3ajvCKuas"
				, "APHmgMYEBsXaPhwbacQwS72ZkBUSEVgmd3"
				, "APhoBGGM7ftHFCN5ZtbtiszbhLQjmvgcKy"
				, "APi7o7WtWUR4qZRtk3yRLYGryBDhieLymQ"
				, "APif9VZ9SWbvhBpmEza1wNL8S4cCEEyCwJ"
				, "APiioTF7HBPYonZ6yc5qf2Jcjh41iuVZWR"
				, "APJ4uTjHzm6QUggvvLmWczX3DE1zNEKxiX"
				, "APj9oc3Fho8jYz9rXeWVG5Awo1NHHHMkk6"
				, "APJaTebadCxtkTdencCS2KLw21qLgqfBAt"
				, "APjC3MRJU5wp6L7N6ZGQweEE2QDprKc45x"
				, "APjhuV4QBfxPvWj5yPZZe5RCi1rbbagijd"
				, "APJmyZrxGgHXQsvoFpMgBApcr1rJSKDite"
				, "APJpTqvmxJJStZEveT7Xhjo1J7fMLNgt8v"
				, "APJxHVTGc2pMui7doUHd53uaWk6bHc1w7R"
				, "APK3KFg7h3XM6pzXiYxfmFMEocBjJyp528"
				, "APk7cuFsswvUChCU6vkeZky3MfwPFFs368"
				, "APKRGVmJxZ1tBSv8B65UYQs7T9ZCDREWdS"
				, "APKsk6meaGbuD51bCz4ZiwJ5GktSCbjCo9"
				, "APKTeMAFSTZ4rcARoL2USHrvst8fwyWryP"
				, "APKVwsLiXJEumN7j79LRezEQTrL7VSDXrq"
				, "APL1uhChvFRh3ZtjnztHqreVCXwFyAAgBn"
				, "APLCj3x6jHqtFM5nrV3NxceStdpGB7Uc67"
				, "APLDTTHXwcWUQkchBankTqmgn5dkckY4B9"
				, "APmDxVCgzauhDGkJ63QJT6Y4dmefbZdt4n"
				, "APMThGyqwQmVGvE84z2f1buqLGS6oLps9U"
				, "APmUgXKSQruvmaaqhnvmVy5GqkKoyv41ES"
				, "APmYjDnZ6TDNUkvCruGwWzei2Ryw2aaEX3"
				, "APMYQskQbTutgMzUJL8ebSxDVhouHfKjpJ"
				, "APN4HXizFL6wAcPuhFwNd9XVBm5jrcdmn7"
				, "APN9NuxDRVNG9EXxxGp4k1ukSi3iFGi6EX"
				, "APND5TiejHpk5pPnAMcR3Vhx4pp37VLbiL"
				, "APnFNhtiP9qnsPX3TEvVprGAmYNCFQzA86"
				, "APNhECeW6q695imiKaERX7gR7F7BJuMH1U"
				, "APnJ2vJWZiEujQqBKLy5M1JMbCue1Aokjz"
				, "APNPdrx1oJWmyv3FkEQJojeNXU27n9dwae"
				, "APNRqtx4HPWB3WRh4RMUgQB2Reo3haX4Tm"
				, "APNSFXRNLWT1gQDkDoaSwq1dixF8k9wygk"
				, "APntqHqY83tqyrNp42z4gFdd8iYkehKw58"
				, "APNwx4nB6GYru7fWP9DKbdWEWrYaSU4Wca"
				, "APo5EyqA9CekPbwaernfnvnGQjxM1KFBVQ"
				, "APo5zr5PvfCXYLtT3xjrYSfxHaMw6js86X"
				, "APoFCuWrTA4VstJ4ovTpYYzCBVMvnsRLzb"
				, "APoLhFeefrTryqVFdY4mCNRFRWLBc4kxoQ"
				, "APoQKfMaND3QoKEhfV8WoYAgT1noiTHWSv"
				, "APP1Ron7oqAMuq4VDjsf5ymmRTwkc9AdUM"
				, "APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF"
				, "APpaKX3Rv631VmoaHDnpNgfLVaokek7sgK"
				, "APPb75CzsVZCSWSZY5BYcWidykHLW9FTYy"
				, "APPfgkTZF87z5wxESowZTCNGwD3bd3D3R1"
				, "APpfznQ7xmui1bcoRWwaEPHeTFkS9dBjqh"
				, "APPps9SPu4B5n1fQbQE7v8b24jpcrD5dd5"
				, "APPtEq7Pv8tX2S9Rm8Cdd3TKGBzzhV5fKT"
				, "APPU1SDz5VwxjxXHJZqHRW8joA8za3wqdA"
				, "APpumTt8pBv1VETtA8G46YJKL8q7AfaD23"
				, "APpypVUeGQmjBuguRW3BSJuvrxY3iwSHtg"
				, "APpzYwC8xF3NNr4mA8YJ8berA2BQfXEFTL"
				, "APPZzCZ9vNZk4bHacDzzdRDSCLHHCK3tXm"
				, "APQaq2sM4PBj8jzTcUxH5sYdxxmuHsA4Yp"
				, "APqGQKbSyYwsNXSDgHUx28GhBWTjVrC9s1"
				, "APQLNH4pnGpBr8y5wQKqTANER74ss6VKar"
				, "APqtzf47LzctfPF6XaZK6pFyC4yrFPyYbY"
				, "APr1B8Z7LjcMirpifkxy3Nef1F8GUvNMBc"
				, "APr65UaZ8hF6grnYmvHTtVvERA8SkEcE61"
				, "APraafLbTs9MMET8fLJTqFrxghjtGTYAeU"
				, "APrgedZYNJNjhxxBmiGbCNUZfGmJc6wRwR"
				, "APRtDvk91rxuqCj8zB6nojsPrZTTJR77fR"
				, "APrvhcPkJrzcmNBQm3pTQPHVdJLWKfX6Jf"
				, "APsCG8XreZHKyYaf5ZdDWtH7oS8etqKTZ3"
				, "APsEUuj5CkxnscrTrp9RDvARUKWEvNC73P"
				, "APSij6kYwGjy61tGV5pRSvGuTVcdxg6Deu"
				, "APSJxyvwJXMH3MGAUrtw8cyngfCcuWyLWK"
				, "APsSRGQmorTwuGhWbWb7jueNXr9vcJYHzC"
				, "APT43NJfUAY7S9EWjLK74wdDSFRaJMYNuY"
				, "APtcG9cDycbnawyDKPX8rTrtXSMHD7V5Zd"
				, "APThsMU7pHNmKNPfbgpRrQewx4TkpgrPok"
				, "APTTnBcANLUXZFSrK2NjrZAestzQgx7y3U"
				, "APtUCN4QU6gMbtfsemtShLMnT5iECPZuGQ"
				, "APTYaHjc5jAHb8XoVQmPUvyytJbeYM5y5a"
				, "APTz7rCnkYGXzReZ4KyDJpWnCmRg32dJuY"
				, "APuBniv26w1PbuaE21E2fMBi19FhNPKans"
				, "APuH8TqyijDfVCvSMJrS92BdtScMDBur3r"
				, "APUMtBeEg8U1Rz9iZ9x3BtjJ6Tb4bkBS3s"
				, "APUQsNtZDyyKAtLDr2s72eWVCbzZvjqdBY"
				, "APutpgMkHRZAy55JzfYzaHGVL1MSiVhA6p"
				, "APuTR2ometbvTYnDggTmkfmCaQjurpkKvt"
				, "APUyuRS4ADYiWjAjir84sT3LxCFrstRuV6"
				, "APVi4HHx7bnjV7r1dCEk3VkWxsgrFo214Z"
				, "APvtkUFdHWJDLU6tSufq1qFJmxgpJQhW2S"
				, "APvz6NSYeZKfHogA6MahgVDV4oAFUm5LtV"
				, "APW25BYtiyKVZ5u6hGzuHndNy5ESVT4Anz"
				, "APW9f3KqhESEK8Xvjx9zTBqPKShiaMCkd9"
				, "APWcdfV9yZSgXWPUTSAW6TccxzKoG2LiVb"
				, "APwhJwnyZtMPBQE3H66jrPdhtRpzjy62kQ"
				, "APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo"
				, "APWn8jgwfw7dF47FiUxy9eThDmL8Vfmogz"
				, "APWTKSmbpBXPkqByjw6pppSMsw1AvuP4dk"
				, "APwuPazxm5okcc4kFqqFuuLGbYjZQGTo4h"
				, "APwVjLCAKb5VeyHGF9uTJWvSujKnUzNKGD"
				, "APwx5FkUPqYTevu21KgRM42cfNHp9GpBqS"
				, "APX1RAicNmh99eFWBbrWYipSCiU67Ge6kM"
				, "APX6WQqueFbgFYXbtvQrnbUgeYKFGFoZpN"
				, "APxDBR3Fw2dud4iwrhB5Lux2aNgHA1xMrN"
				, "APXHpdTbXJSjGtq29dyYcYZSyRf61LnPeZ"
				, "APxSeNZq2smN9MHbg6DhuHMRhja8v94a7a"
				, "APXsGiYHiJJXdZVKHHKMBs62ZSTg5yvHjE"
				, "APxVcaZUCDC1SgrqvE3f4xTrjdf92Rks9k"
				, "APY4SjbE49MZGAVWGA2jyXpFPhrd8EDPy8"
				, "APyGZH1tR5VdtaZRAkwGJC8hNQdMdc4aim"
				, "APYKVZwe3bnhwcu1VZpneFHfUKJPfxnS3j"
				, "APynD7p3TcLTdzeFvhuv2PfS8u5G2jT95Q"
				, "APynyrXAcsuDnj7m2psyxP3H3UkBcBWnrs"
				, "APZBjjW5TKsSXwbjf8ysvq4UXvP2odPS9T"
				, "APzcdHefP3emqWUkJ2vbn4eAwrDa7BenCt"
				, "APzFMvVYW12k97pg7ybYPqj5Hd86qytCAC"
				, "APZFzshxRLtWkTz8L4uDihCqCoShVMN5Ti"
				, "APZj1VurgsmP7Z2Khy3Ln3pHxJvmVHsqiP"
				, "APzJxxKB9CQY4CbPpz4Vpw36ZQX9oAeBzs"
				, "APzkspCh73ysbkfDXjDE7aFUZkhFLGiBvi"
				, "APzKYkJjopKLp8TEJmnJBNgXE4Xi9LNXwf"
				, "APZMPT4KQp6gX4Z2ADGTECRf1CKLb95Fpk"
				, "APzp41Ss4r83whn3m1hnv3oncSEEhSgTWP"
				, "APzqQJ6F2jhYQ2srV8z5mcpFZumfAm81aU"
				, "APzRr3NQfu4Vm6Ub1WSzaVnXrFC1KexmLh"
				, "APzRxydJKgnQvtZPY7ewBeaaychbW3np41"
				, "APzvHUp1zJFgAnxnQswB52FcGGk2ZvFfL4"
				, "APZy8NrFeCdP5iuApKnuFGscjxZnjGnPTC"
				, "APzyEAKUsfjgmL8gT58tYCjA7qG8dgXKcn"
				, "AQ15poKBqoJdsJDYerMH1uRC65VRAQFhbL"
				, "AQ22XKtQSBPMCgWqmkALorUStNAwFEy3XP"
				, "AQ2DSzTRYQWrDoZjMGy9eEkihax5M9RYPP"
				, "AQ2GSqAxyEvgvrjPCUnTH3ghHtvF9bEzVs"
				, "AQ2toNwym8ySNx5Z3ttt8n2Wjh9LLHQS4Z"
				, "AQ2xAADYoQLjBhcw6Ui86mkLY3sUrLu3EZ"
				, "AQ354As5irRTeArqBK3v5xQpjvJXgewYit"
				, "AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8"
				, "AQ4ELYnNoybFroiXgooCQbYxDnsBVGcwtM"
				, "AQ4HjiM89PtdRSuF7UBEZDaFcBPkFHFCK7"
				, "AQ4nxAxYpPP7gNZV25nYmT17ikvnVMVvLx"
				, "AQ57MurqAcvSweoxaeGFySa4xaWZFPJ2Tx"
				, "AQ5gJwttE9DugxbLHiW8AcRs2JKVBEc5BX"
				, "AQ5NZArahJWQSVup3C9sU1DTAGPXBqPGWz"
				, "AQ648ssvLAejrBMu753nes3YUBzgQqq5hN"
				, "AQ6DQVKBoAWMyBb9XGo2Vjju8cYyaDfRrX"
				, "AQ6NZrMajhRszMr6GyvCEshGdEFgMy29tz"
				, "AQ6Q66sd6GdXBVii79otebCoWSeiUsMNqT"
				, "AQ6VkQuZ2G34HmTCsUBPW1wfaXKSx7rq79"
				, "AQ7CoJtYUmiCv9MFqBJRmoFCerqQ7tbUQD"
				, "AQ7nHDrMARTKFJ29C4sRLZGfDwDbWEen8H"
				, "AQ8Qo9NTRRpTQHAXfpiFdeBLtdzkatM1Gb"
				, "AQ8s2TTasceHWpQoAerWE2aMh2DYxvMhD8"
				, "AQ8SKtmSFcNByJjaYEyKwraUn77UHW9RmD"
				, "AQ9dFxYgS7pPJT6F1izg3iYjmQYNgedzT4"
				, "AQA1g16knm6Y9oFgZ76xM3pw9Y16nuWsB2"
				, "AQAAMHMCyocaqHW5QPF3NVtvHwggcdZSio"
				, "AQaJkWvspdDkhKv6HjJa4r2YvneW6jQdtJ"
				, "AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM"
				, "AQapPsViPLdiMZ8yCjcYpKwQAWasQqyjwK"
				, "AQAreP5jCvGL7pr65sPEWCtkdQUtgFUMTC"
				, "AQaV3MxdWTLHVixurs2uCbKdZ7vSnC4JLi"
				, "AQaVW3jZdVoemMSQvoU9Q61jGJq6qzGKha"
				, "AQaVznZ9uJ4pjw9LEnSjDJzauXLuLbu9KP"
				, "AQaX92SJPE4uRi46kKiyUxQptU6JW3Fus3"
				, "AQazpYvdscRCb2r7xvjczsYWVE2t5nxjwa"
				, "AQaZrV8exUQF9oGogHxHcdQJxrJTPfeKfZ"
				, "AQb1TQ8nU8uakv3Y3uCv9rsecJsCBAvvNr"
				, "AQbAV5RfXZobrHENqrMxQXT3zVvesCUgbw"
				, "AQbGuWMVPVhRPtVtwZpGepDEZtFeFFGj4p"
				, "AQc6S2jqRn7LeVRkPSd7yYhg41Xc4dSSnz"
				, "AQCD4DxCgvQJYM9mG1XHavDE4s41qC85vp"
				, "AQCj3eZyKbceCaSfBrmENGQZqujbDG9BjP"
				, "AQcjfaUQB6nSWGqSzzSmsjNHibDpEFb1vM"
				, "AQCnPRAunXCHuv34Z9eEdbobpH1cG77vH7"
				, "AQCUs5kFFmnmKMHxESb5wiD467daYMhh4b"
				, "AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx"
				, "AQdphurtmscSqMPrSVS2GFJ2W1XYSxhHeu"
				, "AQdPvLFUAZYhAeiDRh1fSxvSAh8WTZNRJy"
				, "AQdpVQiAUxdSp4EbVV56BxJ9gBPvNVYmLv"
				, "AQdTZtbxDaXYs8x38qWtwzQM4ZXcX5LDkc"
				, "AQDZF42wsLvZNTpp9pKw9ee7twLhQGGUQ7"
				, "AQEHnJAvhT96i3pTrvJnDen6B5RUy3Zc8z"
				, "AQeLpfS95XGypDWD2zGRM8gqLbwYepkc5A"
				, "AQF85AwUz3h859TyxBW8eSpFh6Ein7vZFu"
				, "AQfABxgpAsvCS464PiS5BdAx7vnjourZrJ"
				, "AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd"
				, "AQfip4WkK94asR5sPuCmfdesve4xF3j3Jd"
				, "AQfMpkKNwRAKrzXWC6Des2ZhVAB4y3k2tD"
				, "AQFpqpF3bqM1u2LBqv56WmVGfVhS8wFy2q"
				, "AQFReNGa921hvm2k9vN1Dxo7vmbYz4BztN"
				, "AQftcBTAXDu9yjVyqrcNMsJzv1iz3LF14U"
				, "AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo"
				, "AQFVbu1eYwFAigK7m4Hj34r36D1LTNDbdJ"
				, "AQFVqCGDFgt9mPKgMVfwJWnmncqYSxWfvW"
				, "AQfyr7oCbytNiTiM5rbhVe4MFgMigf6dQR"
				, "AQg7Bu7gxevUatPhq9cPUeDN5xvK2AU2Ky"
				, "AQGAc6vaP6zHTQMZPm7i27e16FahCoCTb1"
				, "AQGAweRGX1DMPsik84SkTo5d1mF2tF7WxH"
				, "AQgxNSV7M3eTN4M6qte9uCjwK1knDmccAa"
				, "AQh57P4AaJKrEFWM32zGGtpvhHAxsoDpe9"
				, "AQherQsPcYjcePajkr94F6qgNZAvJhtHp2"
				, "AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u"
				, "AQHj22QNo2nLQRPvBAkXfmTvhZDMNerFzf"
				, "AQHqbxA1kzhT7SrhCiXZwn1xqELzVRYgP1"
				, "AQhQeHJyvkvh8J9mPDxcrm7RP5fwZQdpn9"
				, "AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B"
				, "AQHqwFNirbMUbmkpEo2BYeNBPUGWk9hRPQ"
				, "AQHRF6jd1hgjRGSpHPq9mwcU4b2AANC1DJ"
				, "AQiMHbfvN5uKWsidjiAbpYh1pc2W6WJodp"
				, "AQioecucvbMTT4n28UXPZ3Pg32tgA4bNRj"
				, "AQiQpqswSCoVa4nM1gW5G44ch3HEGjp9FQ"
				, "AQJ9ePry45rVSesVyAcKDdXnfR87xLKU82"
				, "AQJFJjsyCm5XdSWHdCnQj3v5vspXy3eabn"
				, "AQJJtZb7SnHCYQSxEF9T4AzbSEqAgv9NCV"
				, "AQJK3x5PngmMrVsTtqVEgwdCWfvopThFt1"
				, "AQjQfguKNg1XeiRj2iDEghcW3iSTf94dJT"
				, "AQJUNuK8p3eq6gTkX5w9K8HLZeQSnftPAb"
				, "AQjXPVbhZoasXmeWCgLPcpKQPxYTbqA165"
				, "AQk4pfthrpuMmgYmJH6TcwEnqLRV8m3Qnh"
				, "AQKN7haqXXZ1E3w6bQkQZTs83SAcxjV6rF"
				, "AQksDPpFKwGVh1awrLjguJvzwmCFyALi96"
				, "AQL35K1QkzJ3C5awFNUet3BWpov1K6GyQY"
				, "AQmEHCy6qJLCLetd2iunL35dv2GYhE8d6S"
				, "AQmFpXHtTLSJMoF7czwEBqj1JsXfvaD5JT"
				, "AQMMi9swsZrefBQwYr9gf4innZhtkq9kuR"
				, "AQmqVVdAAWLw9t6Ez3fh5jobyy9fiaphLP"
				, "AQmTTuYygrwJev4LAa7xF7woyTXgRjHxuV"
				, "AQMvYVQyYJLLCRfDWqoYy3o6nzdGFgUWPg"
				, "AQn8czSVUT7z8BaLsjrs7pmkhP6v2q3Een"
				, "AQnDSJZL6WEtSGHhPazgxSDYfNymmKHGox"
				, "AQNkadf1Fx9xx125tAmSs9axc8EbRhrfLS"
				, "AQnL1f3YhLMS8qBZ2qtd9CkrY6psAECAC5"
				, "AQnoS4kqGM2vnwQyvdBFJf189mDX8h6FJs"
				, "AQnsntZ5jobN9WircDVrh3tdNsAJ1APV1S"
				, "AQo5kUXCmYDcZQZSx1p6jTGh5Dcinetdi5"
				, "AQoDR9EC2U2aDGdrNyWkweFSdpi1VP7J3U"
				, "AQoMDAep3mYLcCRhHuXJvJMdGe8W4TfmeG"
				, "AQos5ZT3Guvam19WQhboJzRZ7BJ5ubyM1u"
				, "AQpM3oyKjnv5ezrfpyfs7irbgbf9EDyw57"
				, "AQPmtmNSBMLYt81xMA6QC7KR6CjZ64HtnE"
				, "AQPMtz6fxMBUaJ9eFPLuzEhvXTt51Q5AS5"
				, "AQpN8DtkDnJfn8YHeeor7p1WyPfJy1k9Zw"
				, "AQpUF7vGXBVjqADRMdDVLf7f2GxwERKzgt"
				, "AQpvBqj9Z3E9PbR3nye3qYahBTHzjUSGVa"
				, "AQQ3ZrByPL6vrdqohLUArsiuDCuuykLiwg"
				, "AQQMhgBdi8AcsmBiRRr99m2k2nDjR36AKd"
				, "AQqQ9iqYUHQ3HHRNinToAPCJGnEgVYAvhL"
				, "AQqRLDn5ADv3CPuE1gMTbo1gNVntcPwj3n"
				, "AQqsPBjcqhwCFEnTdLdUGHQKGMPZGKwzuK"
				, "AQQsxc2orZHqyJZpfLKCS8EoCuJDH1xVy1"
				, "AQQttkJxV7Rb6znrZNHWSRHV2XYR3AubQ7"
				, "AQr6Qu6ZS2zJiTv6wUTqXw1jXK8wwurpV3"
				, "AQR7j9bVdUyUP9ZDhhydzm7S9iuF6x3SVU"
				, "AQrfJMpKh4oxMbG8bqgeE9uXwd6xNWQCCS"
				, "AQrhYc51bqDZehpvBFimChFyLQQXbTuPeu"
				, "AQrt39yZAHyrWuAyFbTyjq7jZSeY17fgsD"
				, "AQrVKMeH8GWV1mWY2Fp4nrFbf1MbcZkUUS"
				, "AQrzzm34EEMXxHRQGTASvz6KajK7Wkmixf"
				, "AQSKauUBeXokySoXXG8Wz6JqWdrr8S2iHf"
				, "AQSKF2xbm4ptNJYQqiiZdjFNn3TaHeY5x9"
				, "AQSr8SE4q2dGaMM6Z4Zxe5a2iQ8evWh13A"
				, "AQSSCkoUbkSuW95jLeAQv5RF1TRdXABF6y"
				, "AQstWdY9H5VAJiUTsakYYKKCG5fny6gdGD"
				, "AQSvPoTGrjqotDv7pbZTAxNwv4EDCXyngs"
				, "AQTDsxVZC7UoHLveqqzjs9zW72oQKVCUy2"
				, "AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN"
				, "AQtTqzCVoQKjF3DPymSLsmQTp4UXJ27wre"
				, "AQufCNw3DrEc52fS6m7sXSqzR6UC1VqNGP"
				, "AQuPzWzkodb818yvpG6Ljn5xdXDtfUEqSt"
				, "AQV8KuU6R5owaAEp3PxQRmTDT65ktZkAhQ"
				, "AQvAcNTM1Y7eoRpCWXT3jURvoJ24e22Luz"
				, "AQVDp9SHeYV1wtBFfE9iQ7EMACGVrZBrSb"
				, "AQVJqJ1nyz7DegZzqJQo7KJEP9NnFhiNjf"
				, "AQVnu2ZHykWxSP5goiLUNWpf37wha2n2tG"
				, "AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73"
				, "AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb"
				, "AQW7pB28HCyWvBBx7CXhmk3hUSw82jRhFD"
				, "AQwTUa2dZncZwiBqdgU4VNySyH7pvZJG1P"
				, "AQWW36rERwWz7FhaibsJXbd7vYVwvyVSyP"
				, "AQxdCBM4N4sarCdeofrCtC5pRXUzrtDqDj"
				, "AQXnZYGDc4Q1GanExLssAcEiRTqtVGWNVs"
				, "AQYbWuFXMa8mfLgB8KGZDMU5KAdCXAUZhZ"
				, "AQyePqu9QWkR9NA7ksCFVPxvhvM45xSkrB"
				, "AQYMqg3Z5dXhw3UZiFcVpJCSn64faECfbC"
				, "AQYQCnTRKwZ8ibM2E9wDvDJDeWKXmGa9Ta"
				, "AQySceKXbjwtP2qd2bXYsQm9ReTGZqDvs6"
				, "AQYsyYqRd88VKWyp7rq6QeTVo9hSEqakxp"
				, "AQYvDTxurdC28oPYhE8X8hqTeysedVewu4"
				, "AQZe4iBERsYfszf93HQ2VbFVTyi9t1X3uK"
				, "AQZLM8DTxLpA1iBjfrxHwESndyUyyV79Wc"
				, "AQZPv6sM6jdZDS82pWUEYsN1U4oYCacMvD"
				, "AQzpZb3PJdBxX8WTpvbz5qpFTSc7wbSHWg"
				, "AQzsupHKZPGsqknhjH4DyA31GqWoUM8iFw"
				, "AR1tPq5zcYhjR2B7rnE2bxofxQiSHQ6vMq"
				, "AR26FcxFBxnTK4M5n4CQHpArkxu4obY42w"
				, "AR2d76J2oEdm4KAPujKiupYjcEHZbpKtJf"
				, "AR2p9GrhTNV8VKUgMVAcNR9VR46vh1mnc5"
				, "AR2py4VwSehusWohDpFv1Mzqt3xUjWEhet"
				, "AR2V4uCDdjZMj1Paf9RLjxhwpgDtU7CWms"
				, "AR3GU2DT4yS2z7vWN995ZXCVvhLmvJzdp6"
				, "AR3KM4YJ35SqvsQYLqSEkdnVHeeiHV3sf2"
				, "AR3qV8Sr2QVSSRNKQZ8toXgZ1yyydUBE38"
				, "AR3vhYMpLMTixqUePjNRixf1Bd4ndKJn9E"
				, "AR3vrNyrDjDdFJJyCHdvT6u8QYnxcHUkFn"
				, "AR4PCkpSUBc6ZSrkgYdmTZuQYojFpmMsov"
				, "AR4qtc82VM4rDMz8rfMtoFH4C4cvC4qsJ2"
				, "AR4rg5JU5xLmkTc32qyZTfU96J6Z8zKPXz"
				, "AR5ayr8jwDXw5hdwA7kUZWD3pjBLbXZv1u"
				, "AR5KkKqaoZ1dAq2bc7FQqkM7NU8kJst51Z"
				, "AR5rGhccZzq3xGCethi5JkDJ2teK2AeyPk"
				, "AR7fc9HEJGFHPjmkf7oZ41Vfu8UX8Sw5Ce"
				, "AR8mXAp5ej4Zn1aJpS5sSZUHgEAN3Um7uZ"
				, "ARA7f6bkKwMp67TQUGD2LaQiqN7YJpHyLb"
				, "ARaabCaQ1QVcU5qFnDVTcweQBDP8ZJzes3"
				, "ARabzRHCmydF56p2aCZtmdqFhW1ZqYBXEL"
				, "ARaDgDR8z1gZAeS5WEpBVfv6oaAHie2pJs"
				, "ARaeAm2cQZqjguv4MRBu653j6gfouzyWbF"
				, "ARAJDGh6hufucpfVfMPBJMwtjt8svF498j"
				, "ARARW2P5mNJuFhenwV9ezrGfufw7Vb1guL"
				, "ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8"
				, "ARawpy9xLGcGX2pjZoAEv4w1Pg9PeNapXH"
				, "ARB3Psq8EbfPLg4msHDZGVUGj2s8ttwTmU"
				, "ARBENRQxPB9biMdei4XEsbWoNMudG3ZBnr"
				, "ARBmbbfNeuEuR9pKyobJB6dacerUFFgcma"
				, "ARBpZV5uBDwrng6sBTGtu3TKsqkhqpCrXV"
				, "ARBuaNwfNXvfnRg4STytboaCGaYcMyUgv9"
				, "ARbuEiUexUBRwNgzKQMuUe5u5BQqiNFPks"
				, "ARC79pkndDgwEDh8LM4D5L8hxbecuCSHmf"
				, "ARc7mjJ2cefRn3WscZ2C3Za9JQMBPL7DpQ"
				, "ARc7poCVXsM5ji9QUhNsznqSY2YEjaE18p"
				, "ARCEufWdjgN1hkiypEeC2vsuW7KydkqSU9"
				, "ARcixVKEShrTnvkgHH8PVMXEgiNhc1VJRW"
				, "ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS"
				, "ARcrusetQnJwn9vPEnh7167UK4hTsANRvo"
				, "ARd3ZqcP2ncSz9PU2MApRsV1Thyraii8gW"
				, "ARdaZnXSpPNGAEgTYPBNQ4iAKGF4FLKQAS"
				, "ARDCr3KWaxzcatzNsDGTgF21XcoZjryrjc"
				, "ARDgJypNXc6PappLBN2R5qDF92th2TY7ze"
				, "ARdTGwHF47TmtqxqAawT2FwhSJxXRqXXdr"
				, "ARdXNAwN6SHtUstBXciFzaNLwgpNwcbE5C"
				, "ARe4HUFQAps6m5d3tuBqKHumi1iT1ns3cr"
				, "ARE7A8n7JfitPcd7PAF5Qo2zFkDZDap5Fr"
				, "ARE7m5RB5ZC3VCbjoBgqqNuhxRtAUHR3kU"
				, "AReeYSDEUdXiUjUSAWNsMy9EWFm1r22mwL"
				, "AREFQ9U9Hxmin8FXpkT21T3WW4typdPJMo"
				, "AREJ8R1v57qRuKrQw1hK2eTCD1FVac16MG"
				, "ARERKsr5womWfxjmT8zesPrM9G5UubG7xg"
				, "ARexnhXZDck971pxMTyJjvfP5VNj6uRRFu"
				, "AReygXtNV13yoVDSgRM5HKz4uMY1VS6JzZ"
				, "ARFc7CXUFH6VpexvDK44rHVRkGb7fLn2st"
				, "ARFL7vJudgim775KkuEPPvBbaFEfVx8pG1"
				, "ARfqx4HvzRBJnfZHCsaECuwY25ticHdRKA"
				, "ARFrJaHaq9g2pxg1yorpTbrRtNkgt1zYZX"
				, "ARFt3Bu3Ey8SVJZzFRM5vuB6WigNovAQJu"
				, "ARfV8VyFoF9H3MK2bj5HdFBkJ1jxGoKxPH"
				, "ARfvajgnkWNd8orh6mHtcsJBq4vfatAaQP"
				, "ARfyYanhtizrC2Qo1yzTMdKwrAoKrRdeND"
				, "ARG92G22PDRJgKTcN1MCKDNYC5dXgQBLhD"
				, "ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY"
				, "ARgD2ULMBGaPwYiw6dtcBmPSDz9PH2rVK1"
				, "ARgrGe9VmyGLWSL8fo4vrt6LYezwNbbMEj"
				, "ARgSiCKV2j5zazidf74krRe8PdjYcgGaH2"
				, "ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY"
				, "ARhcXDp36Q3DYpHefek3uQ2Mx1e33tpUST"
				, "ARHEoD7FCpm1yGwqFoYm6pQrekeghq2nEZ"
				, "ARHqiuiaRfLgkXtNUGLHADSPjQsn4ws2tR"
				, "ARhRqr64W2XVNLXCKmaeSMcjay5R36sVvQ"
				, "ARHsdvHZmNXqQjye3zKfEchmer5poLTd5b"
				, "ARhsuZErgoZuwQjGiTzgnywox2jWU5f5s6"
				, "ARHVHFLetCYg16fKcLUn6GejnQk8eamC2M"
				, "ARi3pL6WEMTY3G4G5xcxsn9iyucrQU93o5"
				, "ARicyQKvkD8bmtrUcaNiBsm9dvUwBp2cb2"
				, "ARiovp1vT7fLAytUzNXEpcatth8bAkhtpH"
				, "ARixTqmtMS1J872MP6Jxd6J7VU69t6KBAU"
				, "ARjDVjwkrXizD5C47iPJ8gJ8Y9JSdy14wW"
				, "ARJfV9HYvuuFmKHFVjWFkhgWMnJcunYtqq"
				, "ARJH2bENapQf6eLQS85YShKLgohKKKNhQG"
				, "ARJszC6YfYFpeKGJnMnQzvFZzbmweRGAP9"
				, "ARJWnqr1Uos2CfLsWf6Mrh5hBWezCJb2Ki"
				, "ARjzGSz6oPBRzdbss5H3EsGZ5Ttz7PqdzM"
				, "ARkdPrXiWZxPVqiP2f9w5BCsSmznfivFGj"
				, "ARkes4GSMJGN32b4FCc39KiQCsP8x8WnM2"
				, "ARkM6SooUDUvbJ1zJ5sAcLth75QQoSEjzD"
				, "ARkMXWdiq8i94ssQjCH2sqBtBbeLYnHcbX"
				, "ARKo3j7VXGUVmYuq3T1sn7WJFmqJ32JBUB"
				, "ARKquyJ6aJbJ4hwVaZHjPrF2ztSe6Hsk1E"
				, "ARKRZjVtkPxpRe38J6th8nYeNLCY1Q5CC1"
				, "ARKVaHDM76tQaMJMwEhzKWcec399z1UhAH"
				, "ARLb6emK3guMhoDxZhpLpwPYdJfCaxBAJA"
				, "ARLHfdrV6KJpmMxXqsMrwgBH25prh1GWm2"
				, "ARLihLtc9PwN2arkQCYRpppaDt4QGcdb2A"
				, "ARLrDMFf3dPa72vHvPMcJSGFgijk5pFvsT"
				, "ARM2EXfresnj9bb69JzmkF8WBQjKjd4GF1"
				, "ARMjVPC5UHKkU828xxKqgmAPNi8XC2wbfK"
				, "ARmm19xirnE3RYhahEfT9BnEAYfiPeNXUz"
				, "ARmoPtsr6YqUuBDhWDy52iL7zaQaakxUgP"
				, "ARMQbPF3gjVSdz8b1MfgGyN52nDENytadA"
				, "ARmqyEwTMyWH6N11bXkFXuERkzez97etM9"
				, "ARMvcTQBJbNUxa57S5fbghU7xTBNpS6u6G"
				, "ARnCpYmGJXu8q74PmJUHrfZz3tvALTmkDj"
				, "ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB"
				, "ARnNQ571tNbFTTkHVuu58EYqVmF1KKbbTp"
				, "ARnQhZjVueua65YpN49iL21B36NKM2b2jW"
				, "ARNUeeToiF6Axk6ryzGcyEGZ5BWxQSpyXU"
				, "ARnUXdBtJiniCSfsTQyHs1KFVtcaVdL59j"
				, "ARNzkiTTptbe66QhuseHPqC1nX9bSaXSAq"
				, "ARoAffnbV5DCLDkESKHehhj3WpL6Nj19m4"
				, "ARoSF6vWFrieLHTzcQQts9TVB8Ko1vVNuo"
				, "ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM"
				, "ARoY5jV2q8tToAyiUSE1uChvreWipCp7tW"
				, "ARoYaRfL9J38rSoYrTd7KJSGVxiYxypXYw"
				, "ARoyv8H8yQqT497bw3hPE6RKtcXCJrzixM"
				, "ARp5xSNpeY5xcoa9ZGzAvsMhXiexcBziwy"
				, "ARPahxRwtAjGdvJb1vnFT3Roh9ddFR1q2r"
				, "ARpB3hEC22kEXgmXHAe5ryEW2BPwbYvirL"
				, "ARpK9mcGznRWXVbabYS8SwDY7Bfm8xniqv"
				, "ARPokYTwKhm1qdghTFouKgqte1LUNtF11D"
				, "ARPWfYhphL1oRb17e2v4gRWFwkMdpjtqfQ"
				, "ARPyHt4m3RJub2y4uC3h1yJQx8pmx5sxQt"
				, "ARq65PaEqfVeGHweVAf7wsrMdzRAuqQnU6"
				, "ARQBr2xbUEfqKEeSZBwaWk3GbULKSDQpmt"
				, "ARQQKkZytbpZE1aTetfttJCzvCunu8GAXH"
				, "ARqUieWPGwTRC76tZWVBRJmcvg5155L7Hz"
				, "ARQzwa9Wjds9mcJB1RLF6zzm53znnJsoAu"
				, "ARrcCdYbns11NvRV6diek9ff3BS8GFb1Gh"
				, "ARReZgdVnKNm1DkfC2Jbv44dn4c6tAVF8z"
				, "ARRJNKap4QJFSKVvVonmaxxzUrdmU2cFSr"
				, "ARRznv6ypwD7Nb5ptLafBMG6x1jsqgj4XV"
				, "ARS7aJrU8kjjt88Gpn54tL2kvjkxxAVVDK"
				, "ARsch72U9LUWME7z5Y9E1ZiQwu4MYqLHWp"
				, "ARSqoBHzgFb8jg6EEwZ6cHwcBPDDcsXAAi"
				, "ARSRE1BBxcGjkAKTnxbRKybq3dtqr9t1M4"
				, "ARszwoHqEu6Bo4GQZmaMo71YPkhSc8BGcw"
				, "ART1StG12runpvDcuDQ4QjdhXceEwYBGpY"
				, "ARt8TRQfthhtiB2ctADVWpbrrAS3Gp8T6V"
				, "ARTD1YKQRgj4tbor9mf16ieA4wQKrWmhL7"
				, "ARTK26NnuyFxoBXnuph3B2jMJeRN4Bp71M"
				, "ARtsFDtxyCpsv3nXSCfTNuwyKsKA5F7Nee"
				, "ARtWfFXJCGHoVPKfLnurX5xAt1SvgwqWKg"
				, "ARtXYiD6APiJmEgAeo774QY2CD3cvuFZfn"
				, "ARTYj9SwvTMgezv8qP6AacFBap4qhoqS61"
				, "ARu8BWU6ZwHzDodcFtzKpb8B46A185XCmM"
				, "ARuDcBrdrGfCxgTp81LCLD27rN773MTj9w"
				, "ARUDpzCGRtWmTRgqM5kkJG1MvNVXTWKhza"
				, "ARUg785ZEBQ7bzm4qzEZ7EE5eBiTfpNepA"
				, "ARuhpfXtoGsd2ayXc8zzb8aybtkUnusdh3"
				, "ARuJWtbygbSbAyhP8TnC2GnMZjnW613ZGd"
				, "ARumjt5qpZKDVEaJjVJqg3PrB9S4SDjZBi"
				, "ARUooJkRZDbCGtUbbB1CM1PvVC6S67dcbF"
				, "ARUoV8NcpoCBotSKqJNgTrUQVewqG2a6RU"
				, "ARUYNwwWqpLkkf9e4KMB9qkcZWxRwWEwGv"
				, "ARv7GHHMMownQQa4cJhDsGdaCYLpkbtiPQ"
				, "ARV822qNodpyDBcKYsZADbSiY5Rq8ZRCqX"
				, "ARV85BpWqjQLGLwA3wXicyGsRvEhg7Av2m"
				, "ARvbFqS9UrYarZEtWnhJuE3Dj5QC4VNUkC"
				, "ARVEf88G125EJBhpWQkxs8FKtPbnB9EN1E"
				, "ARvkkamqBZxRKVrVjJ5QJbHGChDPdCPgNW"
				, "ARVrwz1J2xKfSQxQTH6FZmyn8GUbE6mtiW"
				, "ARVvqeVtPM8dEUebJgA2cBoRfHywVSJJsa"
				, "ARVWSpdNvXWp5taVMRCCsc5ojeCUTXtScT"
				, "ARvYFZkgoTHfxuwzKUBDHRKFagKaJ9L4Jd"
				, "ARw9JGhGww1shPoonBMRd1MnEgGi5QEhJa"
				, "ARWNA2ygS1951kEdmPdh73Uj8Bbvos1G1B"
				, "ARWNDMs7TtyDMPvkyNzk7ihttCuXbQoYzk"
				, "ARWnmofGE4yt3JZLdBHLEdQKRg125XBpga"
				, "ARwsA3mNAjyjT1ngBb5X9uVb96asLiNodo"
				, "ARx2KJhMbxTDNVr1buojzAuLWp342G2vDC"
				, "ARxCj2PGpJur1Lpt1vzGwQgrDMnuBwpSMi"
				, "ARXiVHA3t4E5MXtKCRWS5zUgUVVmjRPsjt"
				, "ARXobv6XQud4GxAfCvnH8Br7wCzGnk2jDG"
				, "ARxvgSEWJ5y63DiueVmKxCsqTHEYuqRNua"
				, "ARxXJUyzQxaeyCS6Wp5ANP2x7J9g6TKGNJ"
				, "ARxxRkkMKCCkq1NAQAcEoYGWVfBJWvGHy7"
				, "ARY2RYm4RhbtZ3eZBwuyB2MjSf6GRy9829"
				, "ARY3NNiKJLYVi3HujuRPuJ4e4BwVNW5nqM"
				, "ARy46cq7yKuAE8zjL5CfaFVF5QMAiusXyS"
				, "ARYAkif49zJfAZZmh3Tsqh6HTSRQFHN9Tx"
				, "ARycAU3dxJFJYxA2P6xYT9szQcticTcKvV"
				, "ARYE5QJMgVeN6BdP6DvyXnwCE125k3Wfrv"
				, "ARYMq13DdUiudjUPxfEN7ZwE6zsai4nqff"
				, "ARyQZfCuFftMkNiBqvyCtfuA81BvYpgM3S"
				, "ARYxfk1gjLYFrX6eNeCZA4BzkL4anEWv8p"
				, "ARYz3Px3MxcvwvVnoFiZLwmDF1PJ8RSuvo"
				, "ARz3Mq41XuGvanUcrLc3h26HvH4UGeCifn"
				, "ARzksBkJCiy5UCwXP1hdZUewdwVvuSFxBS"
				, "ARZZp1NP2qLjhQdhHD8SjtVoELu3rc36sv"
				, "AS17VcxuPeVYx7ggs3F5hgFh2h83zrWUWJ"
				, "AS1th4KuTTCScoTuCw6GuxXdAvgvZ42r9z"
				, "AS2D7trnvtTLqDDGPNjhyZFx4EeMFGPArR"
				, "AS2ismJtsAdPrk7Kcers3RNsVZiPTsDxpo"
				, "AS3h8RSztGaqkvSAHWEjqGp19cpMLZhCnp"
				, "AS3jaRBEtc1F4nkgHmR22MNokX6dT5B4Xj"
				, "AS3RkxMjcEzbZhaMoWC7SEBnSRYoJW1Fxe"
				, "AS3XsAfbapXukbT8B1U2Bh4Ld6ehwcNNP3"
				, "AS4o6ERfcvmv3yCZDHeJTuaFwXF1W9Mq7o"
				, "AS52JgUzT2nuRJbNJTWcH3rdPCXFBxrESK"
				, "AS5enPj8FSdk3HnCndToPLr4YjUTSVEnDm"
				, "AS5rA3fu4MajXobioB8as3qidTWywqV9XM"
				, "AS6mGLSh5GcxcbUimzaCsoxDjqBUWtJ6jS"
				, "AS6tQJzuMyRgFoeZKtUavs8VSEjHb4zeH8"
				, "AS74ntAgHWJXoXh81qvLZZ6oSc5oZQeANq"
				, "AS7Ad8o2LRiei5zQivukJN7PDzomxhJRjh"
				, "AS7gNoqk6NePBM8N7PccYpWBqzKfbiFMWT"
				, "AS7H4w71LBQQGhaChNconaFPA71rL5XdNQ"
				, "AS7i5gayQ4BDPGhkondf8pfSBjseZvJdjd"
				, "AS7QKRVVocityNbpy59VXf5Nrd5WN3EwQx"
				, "AS7STVjLafLDm6KuFSEMEFZRuJPaEv9QZA"
				, "AS7UCmEEgPGC3MqA3thRCZDGU7weJfXwLY"
				, "AS854Q4t1jfN1BeFxq4kc1sQD2UW355iCY"
				, "AS9JaVuLCYa9U4DbtFuehkk673VNkHaBNr"
				, "AS9rrQ5QhSUoBHiaqR6JSg6RhbhcrrYDJk"
				, "ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent"
				, "ASaBqSkVrmw4YM36SmkYZr3Toadf5dqvmH"
				, "ASAhNmceXsjxYR9wn9EbmXwBjBCJ5VbVQX"
				, "ASaNFyyAfhy8a9TqnBNrLEqh2RmsvZYh8S"
				, "ASAPKYGSn8Vd4DEqqG2HVuGh7XAf1k2JJH"
				, "ASARpfrDtxe66bqh5CxRUpbcc7rUuG86JG"
				, "ASaswyX6qraxN3kDC9Mdgf2B8JV6juN59y"
				, "ASAXRgTsoCdVLn87QCn1jgjmjCnZ85uyvv"
				, "ASaxYYdSMjv8ToMn9h4WpJN9TM4gnHp8oT"
				, "ASB6WNuJUXpvp3xemDj3XCZ2BU2rxQJD7c"
				, "ASBgcJymPGhm5YDSeAbRLrZ5et6biKCc4k"
				, "ASbmSnsA6yH2uyJgqgJ2aNrdAdu9YmVcEx"
				, "ASbmzfrTDPDvamxwTBq4YP8M87AtkLvXTi"
				, "ASCbH9KyLeKtJpfcnE8NLkBn9k8TS4aqWk"
				, "ASCcb77RFkg8uLEmNXbBKEx2ApRVWemSck"
				, "ASCgvbKpfXhRRmbFnmHBRRmwTPkJ1rwk87"
				, "AScKiG3d3ZKCZHaVenq1QS3QG2FheoKfrz"
				, "ASCpM4qoDNatRZTf1QxSEFBWjYM6EmHQkW"
				, "ASCUB5iTuBLN1wsRBwFtudieFwM6zracLe"
				, "AScYxTCVszV6Pm7vU6meSCUZfcVo2uCMds"
				, "ASD3grYtgtg7zEtvKyFPiRruSEdHZqkY6a"
				, "ASDh7WAWwyA9HeFJWEWstUn2NotTtgGko4"
				, "ASDoYFmLwUTCaZRyRHfEX1RUZhBuPVMgUo"
				, "ASDTLoxWSK9rPqCLDyyvBmDHMYynSWGTd6"
				, "ASDu1Hs1umAzxo2oSSG8URvm4PoHRrU7LH"
				, "ASdUujpooykub5ZbHSj8iqAhk5u3NMTfL2"
				, "ASdvRz5ptYuuV7VvHYxyTstE1GvEyZqusk"
				, "ASdZkVdQhsWrYyZJJphVEzCQxsXdPTr5dQ"
				, "ASDzYuF5Ur4nzWt7y17mbkobmVcVrgNNPb"
				, "ASe8Z68cSqw466F6YkgjTo5V7qH4FD94Ht"
				, "ASedTXJEusnYvHsF8GQSjTuX64eMLyvVyM"
				, "ASeu3oVrfp9C11E56QCMmjxkHksMRrEoWQ"
				, "ASFerQRNdS6sDKyo4r7US252W3GZ6sEHZ1"
				, "ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC"
				, "ASFhgWEycyLpD8RBALeppsZZwMaR8iAMsw"
				, "ASFsNEUmHPTuUcfthTZkznYRsNroDXFPQ4"
				, "ASFu1aFZF1CnWBsjYEGmyqsC997s1Pcfqs"
				, "ASfY4HcUwAqKeqRkCdVdSfE5vPmf2YfCzL"
				, "ASfyyD47qqssp4uvpkGC6BURyPD8KC4WCL"
				, "ASGA1x4UyHuxoAekqTmjC75YaFZRdWg2AF"
				, "ASGb63csYkBpcucrWxCG7TAW8krwuV9JEL"
				, "ASGDCw31rzk56MUs7kFDH8arXX3kDUBhnE"
				, "ASGdzaFUbhrmVw39tytkRZLAA8wdPmhu6s"
				, "ASGerGjjjdXBDxUAQZ45QySSDtdVpqxeVC"
				, "ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ"
				, "ASGr9A6yxqBXvMFLjnNE4y3s4ebKzY4QSV"
				, "ASgXdrmZ3dUF6DejfXgGVoxAyCMx3ZWVHb"
				, "ASgZeVqZtNmG9APcP9WrquiSxAarsJdx5y"
				, "ASgZYTVUshYr5R4rCfBNjurdEhuvzC6MWW"
				, "ASh2Btk8NkyYCcDah9gDvUDTm1QBxfVZuq"
				, "AShBVm522pFJ7P3yEgSyNnMgdLAh6vBtfS"
				, "AShFb9fxAtLB1AxnnHNziP4LqBNvDnaCsF"
				, "ASHrPyrFhMv4HsnM9DHk8Lw8cDU1rvDxkG"
				, "ASHyQNEsUJWPn6TCNUNoYYVvCKTpzXLks4"
				, "AShzGLsaZ84EdxVqAK27cABTt9v646mCT9"
				, "ASiShhbnLuAKs2rXZjq33epV6oB6jPtLJp"
				, "ASix2nFFUDRe8jN32tQ43bKNxBJYJY4x1q"
				, "ASJ3uejHiDDCahb16foUcWZMp4wC6qt5FV"
				, "ASj4Hz71ipgdEWiGPSoQv2Q6XUmRJdHEm1"
				, "ASJgzdSzqmQMGSq49UN4f3vYWbENEN4qmW"
				, "ASjHjEDweDmwjtpuWnjir5fJGRQ1Gv1bcH"
				, "ASjJs1oq7FLd9vfgDNP5JhNxMEWuVaUpJd"
				, "ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX"
				, "ASJQaSkTQHtiYcP8Vn8L4PPe5ysmNrd7DD"
				, "ASJSEPwUE9rB4TZVAHq2t4tQtiDYsRgJeR"
				, "ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR"
				, "ASkQxaum37vSXdhUmXc5wmmf7fuTrkfczg"
				, "ASLXAjNAg2ZoeznAJGFrh1oJi9aC28e456"
				, "ASMhhwJyFyt37HsQGx511oRvm7vrVvWdad"
				, "ASMoWav2mPdNm9q5H4WzNNW1mWwkvEERTh"
				, "ASmRAxEBtQGaMwNF5dSmyhjtNvBCo9G3eC"
				, "ASmuijwFJC65cbamMPJ4YNgwapagYEvLcr"
				, "ASmupGHrzpd4KBsUVBQLaQcu3fP8NUMpaP"
				, "ASNEvB5hTYzDZSqHestVjQKHCakxCJiqj3"
				, "ASNGYh5dBMTwaqDyhiVVQG5miQz7xdK7kZ"
				, "ASnhMF6CwXpbm97VgBakVGYnSqTcn8Bkac"
				, "ASNtzwFDBjdSnbxL2qCPZBzNo6TtSNCUoi"
				, "ASNUUEozsCZzxXvRA4DjSqin9jwEToWX2N"
				, "ASnZN9xXkAUSSjmazbbGnsZ3E8XscmYiaR"
				, "ASo9Xvm4fxrbGktnFzy8h7v1hMgyBsBgew"
				, "ASodHwTfvKRvq8ZxPLrQDheC9sYuPYzxBg"
				, "ASoKf4tkutZFZb4EcBMdJzyeQPCXBi4C1B"
				, "ASoQbYMoJ7Ggm3EkBq3aWVMGVFpyzzT6GC"
				, "ASp1hSZoCMEgWshEjB4yvBPmbS3Fk2twxM"
				, "ASp56aUPqaQBBb585viwg2cjW1DMwWjuZ7"
				, "ASp8h1YBRuMU5fmogYic2ucke81ioCT1em"
				, "ASPr68UwgzWJ7iw1WJjTz2u3trVjaNTzo9"
				, "ASPYCWUswxHtuM9DgNmAC6G1krPH5LGK8z"
				, "ASq4mZGKY9K7PtuCcHRr8EGGjd1NSTDCYP"
				, "ASQAhvRjw6eDkrqyq9qMt1QE4rGjBsnapL"
				, "ASQZoDnUTaHXusWBRJRwptjkZu8vWLKYBa"
				, "ASR5xV3uz2kEHvCfoAgvmERV9GUs2g4RYd"
				, "ASr92yETWv6PQA27Z2P8ZzGBy2g6qJbTEc"
				, "ASrEVFmRAdSxAsazpUw5AGL7nuoTmkzk49"
				, "ASrj9m2B7j4XT7DPEx9jx4p3WFKKLWgACF"
				, "ASRnGcumkbz34pvQLZeJuxqH26CjAMEUWw"
				, "ASRqUGoBMFCqLuaxjuMZK3drKVkYt7rYSo"
				, "ASrUcYNKfhQW5sMW1y57R3RAan8wRCirgp"
				, "ASrZq9YevbYMYEdQaQR1vDqJCAAkuw6s4s"
				, "ASS9ShDN9oMgd22rz5Vc933BWkNiGiFDvJ"
				, "ASsfKrQ6fHtnmbdddYmKCfNvBK22myUUdF"
				, "ASsG8wrSo7cXKjG5m4fZz3EgrWpCW1SovU"
				, "ASSJpNwUjmr2fz2N2RRC6vYU7Y7TbZUp1N"
				, "ASSQbh7xrJdvb7bo4HpsniTYxpxcZZQFUr"
				, "ASSWvMMUx17LxUbvArtMnHHyoK3Jvjf1UW"
				, "ASt1PGvZvxCNQKJj4KexnKv9bFwTYDeCu2"
				, "ASt8kWNudLWVm3FdS49Jzj3H7ysGYXFpF2"
				, "AStCu92c2XR3HcZAK5F4h4US4EMaPPNQ4h"
				, "ASTddNcK9qP8nCEqKUTzEQaq5gtEti5oAh"
				, "ASti4xXxJUUX9hh2dAzaoGxuRUct1Lm5Rn"
				, "ASTnP5BkouGkPYbm5NPpdQ2WBZPKzR5Up9"
				, "ASTtg28Ek3uau4ajDooHWrE4jwJCvLgxfJ"
				, "ASTwVYFzxbXfg1umZKNd6Ax7w2kWyzPgGM"
				, "ASuDzijD8iM8W3wjVEbLPjkYkU2QyyUjdi"
				, "ASuiWJx2tysmzDm3EcXG1mCc5sop6QA8X8"
				, "ASuKuMvZdTVP6pfFCVZU2iqjNTCzt4k1X7"
				, "ASUwBQ9mFjbyJ3cXsLRfwup5mqePrxYWRh"
				, "ASv5j8tnbhM2nwU2AD74GjxLLVmVqcghTJ"
				, "ASv8UPTiqX8bayUYHfVNBKipWaeYyVnW1d"
				, "ASviLRYxMiXxPvW3SbCjsEPhe9oLCzQHrY"
				, "ASVTRqbESWky1xu2MTHXo177uB5k175Erq"
				, "ASvvmzMdBuetWPRkaJjC26Q6Lcf2NWkF4v"
				, "ASVz4eay1hVj7enNuu8Cs3ho9MEA8GG4VH"
				, "ASw6f3WmhMihXh1kAssgtgnC3HuQYbsEwR"
				, "ASw9gJaeT9bU7vmKvXyyYDcFCUmmHwztwW"
				, "ASwvZDcCa5btZwxNW7xk3t5dYxZpUjiSKn"
				, "ASX8CjtbWnCqXvV31rtixhyiCrjcuFqvZH"
				, "ASX9RqyacPT5LRKdjWPinNmDD4LEnacDf2"
				, "ASXAcgz4WuduhrkYRTRxg9PbZCoJjkjQmr"
				, "ASXdo6bd6qUujgimykwjVvcyX7YbzmyVU4"
				, "ASXM5oRa6P8Di7tKuvsvTT7mbSMkikxfPK"
				, "ASxzH3FQEXgdnMNQmTpW5Bov9KviASivvJ"
				, "ASydtvqGhD3aGVJ73sctPDoEUFHmNPexKo"
				, "ASyHndcNoZrE69iqotZiV1cHfUstdvLmt2"
				, "ASyhzKXuH6ZoyRT29YnFiRsWBiqbVk8ZYX"
				, "ASyJH8fQvyMifeBcktpYvavKGtC1NHawit"
				, "ASywthKajuYoRVFP8eRA5L9HAYWfzyoeVQ"
				, "ASyzXPaQdv3APuiwmASf4BMxRBxk8aJ1oK"
				, "ASZ1cAMzjgLvzCBEsH3ErLvfcBcq2Qgg6f"
				, "ASz5WSwHHiCPndY85LwapYRXxdohp5TkM7"
				, "ASZbi6pad2qSv4DS3PKPXset4qX63Y9rmz"
				, "ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16"
				, "ASZhdxSzMBs3DAAHNRegQ6a8qqBJFryuFj"
				, "ASzmjZkpVCWn5VJHxiwUn4rzDDP44p63DP"
				, "AT1jrZtaYF3YEhgXtihoyYcMUaf35z4GSs"
				, "AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2"
				, "AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9"
				, "AT2m1rwCbXunW5pSiLJuUeZdB9K6KDzpYE"
				, "AT3MfDhGfoVKZ6qqzJzwwsptMJU9iPkHWs"
				, "AT3RpuXSavbUNypmPw2aLaS2Yh4kEisDDn"
				, "AT4oMsqGXdTrZaqaeYm9DN5NkWjobF77dg"
				, "AT4UXU5JMkPoSKc3MnaLTPSb9FTYDQMmmH"
				, "AT5HCEbHYQi4o8DuX2oAooujcRfDQACNWT"
				, "AT5KqMida3nzTbBY6Fc2QBabWsQ7w6XEEg"
				, "AT5mXbW7osmACvYyGH9HRfuFZAixUAEaQm"
				, "AT5P2x5ZrcNtQMZ2fWxrQ8waiLYv5a4bhf"
				, "AT5TXvK6s5cDZzYQsCUGsdGnRN6VsuSEwR"
				, "AT71RoAU9sdA6zYum8UdK1b4wzVA3r3QLf"
				, "AT7SK5xdPhd66UqNkNBKmKFfXxdqPu13B7"
				, "AT7wxzsyPoHNKAzoyu6ofvLKiU2FGGZwvm"
				, "AT8tbaD3vpH7wz6Yw8iNbH4ZyN7SvWS8px"
				, "AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj"
				, "AT97P1opmMHmrqX7MS9gqp6RuF2C5pgTsc"
				, "AT9t4duWwa8fRnMQmHaz3ZJLzYaqyUo6Cg"
				, "AT9undynPdpXJVhQQsfD9th68QBPJYkNTD"
				, "ATAdwS9Je3GNdmGBGV56fhi8J6d787N1ZF"
				, "ATAFpQto3g5rtM1vCXncrW75vzzX9yHFsB"
				, "ATaLYZAMvs4Gc7WqU2Zw8E38WvdFTZZBVm"
				, "ATaNUUvezx3qnGkhT4ZegEdjquxCyHBx4C"
				, "ATar5bvaVGHDi3i8dZBoGtAomukRxAcAHU"
				, "ATAyxdKq9es5cwd2Z7yPnLNWd9ZF4CVbfW"
				, "ATB1kpThLxn8QvQZekwWbrrRgKzGNRw3o7"
				, "ATbmZLnUMUjUg5xTMuHjpuPZPw33VX7fVy"
				, "ATbreWmW8qcu1sN3exVSaHEBdQ9opj4FVL"
				, "ATBwKQ6hxNtGF8hyLk9jcVKBMXHK1phuMU"
				, "ATbXpofM1bvKkqvQNk5cjvXxEGnwJSEmCm"
				, "ATc32b5xUAhFVWLpxaFs3v4hJBVTxzpMA6"
				, "ATCDSEqBZDXnUptBtiJcsF5J4M437zRHWU"
				, "ATcDST31nmw6u5yCEb6yS4nU1GaYcPsQG7"
				, "ATCEdFrTzU2YfczZwVefcm9ermf3ixBhS9"
				, "ATcEpsCYdG2c6917E2YekFAi77JLUwmNnf"
				, "ATchmpYkbeG8k5gjUVNqUNn9cJfA5MJyeK"
				, "ATcMqLTWhSHV4obKiu2bAtFV3vZiTeGEie"
				, "ATCPaNKGsreRPk9EQugDLwhKaQoTcG7JyE"
				, "ATCRNiHq7BQsbdP1xdfWgcQnehjkyp2jGA"
				, "ATD85dx1uyx66m1ALxdLyhfHf5vwN48Ftm"
				, "ATddfzyET5vaCRfhFPYEgYon8duTPQBKwv"
				, "ATDHwgSjF5jL6QrXdtuha2h5zfBNSXNzMu"
				, "ATDKwV7cUG66yDy7DJJKgNEEmb5sVRCWEL"
				, "ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy"
				, "ATe4u1Rk5LkNpARQCHkxz8rb9YXhCCYcZC"
				, "ATe9Fo4MJKY6VAhgqEqGLndsMzC8sEpsXy"
				, "ATem35AWx5NJEW7G3U8vF1efbyw8ZbL4Yr"
				, "ATePi1E5PMMWTmRRvNkD3uKFqrfNNf3yJ9"
				, "ATEqZ2iQC1vzSuXwaDzp8fjbqnKSraGhSJ"
				, "ATesSkSF5SDEpGwoJLUwNx33xu8ruKiF9i"
				, "ATEWgDXw17tTMuPrF3J2mPs9KhZ2jKWt8b"
				, "ATf4eHKUmb9XQoDh8ZQ4BbjSWA1t3qMcw1"
				, "ATF5c3iW4BHPwaBi3pnrBcojNjqcRLK7dW"
				, "ATfBP3dmJG5au5yy9vqM68ywehKQJBR4t9"
				, "ATfbT3Cm99TzS33fLVyGDkpAcKP5c5RC1Y"
				, "ATfh8v1DDZMSAshqP7A2B2A4ueW9epBsMs"
				, "ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX"
				, "ATfqVCrjHFyvA5aCifbZe7YNuqEKV52jFH"
				, "ATfxZEVBfGDA1hCfM1vpuWMd5YLFwdhbnS"
				, "ATfYgAcBTp357hvHsbB9VxRZoTT4Y3MpcZ"
				, "ATg3Cg1AgUe8AniGdqAeip6kM34v9r3HWP"
				, "ATg87DLX2ob9GGnWEG2t9sc1ao8M5rMPYh"
				, "ATG9HYgZfYURgKdHMmNyifESsDF8Qrecav"
				, "ATgA32rhP8SBUgKcxnUTSPEqbkenbLC2eQ"
				, "ATGfpqwDrpM4yMUH2RuqKr7Nxzua7MjF7k"
				, "ATgQaGfmxGoF3cgRhi8y47TJNVeXM1zkZN"
				, "ATgvVwdkNeyFL5Q9sz6AL1c8Sx7AWQ5GeC"
				, "ATGzNbVc9E54Zcv89rPTmki35Nsu1rvS97"
				, "ATgzQZqiFn1EwwTkELbqDUN4eqCCxtog7N"
				, "ATH28N1kLeVj4QRzZxQv1MjYWSBEX2d8xq"
				, "ATH2Aq8x2gdN926bEj9ULrY61dpucnXkzq"
				, "AThcfbiwFCPGqka6q5csSDwBx9yZK3wvpX"
				, "ATHjyoK3CWgtNVee98xcdiAX84Cp1qhw7K"
				, "AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ"
				, "ATHMUCYU8HLPj6V3T86Ej1xUL7uz8e7sbb"
				, "AThNSJT3nR34Thej55qZqoN84KoN3tApr6"
				, "ATi7Ye3QKTpzzXtEyZ4yYBXLYD6VdgNkAo"
				, "ATiLAvfrT5k2G3F7nYPuePK3E9Wm56xkA5"
				, "ATj2mpBZEPgFjQ42HXqt5eAMgAi9pzfqUp"
				, "ATJDZrrEFYjRD5kJ6La57scnY6JiDAucdG"
				, "ATJGncTDgcQrcBENbCRnQvoVrAMP83yvDR"
				, "ATK4yv3QXANMazvzxFkL11YRvXwnGPpcom"
				, "ATkG97ZAPiweD2KvHAt7dEfrcduetQX64z"
				, "ATKKjjEtwZnVha34gYB5gZWHhiFYwTgz8m"
				, "ATKMdjwGfTdEUBWkRguPtpSqoVS7vwTrwt"
				, "ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg"
				, "ATKQyC54DjsdyPZioGM3sXE4K2RrNBKA8q"
				, "ATL5YkLp91B1iMJSf4XR2Ytkaiicv44bNa"
				, "ATLMFv52GeRkoLXyWsVrqFBnwUrd1fUPU6"
				, "ATLMZxo4mxavpcNepC9wmb9k9tt6GSxtHN"
				, "ATLXVXwt9TAwfojnfPyJ5LYXcShfqn6PVt"
				, "ATmgQZGDJ9rcM4FgZFADR2GZs2dAtp8eug"
				, "ATmmhQmCFyC7fmYqcEKULApMhgZqPsuMFm"
				, "ATmt3Gi8k2W4BJrWqvjdq1bz9vHqBB554C"
				, "ATmtZhGjTehp6LfZnREWCDS5SHSLeTKCW1"
				, "ATmzShtUZViUpLwFwhFHh9bBkyk8FDgW7f"
				, "ATn1L5vj87A7sqsP3L9pSWUFbuHYYNfQQk"
				, "ATnAx1ejD85wySwkKQZPboP7Lj7aE6jwAP"
				, "ATNkKZvYthhCFAA1pAkUNAeULPfw7MDdV4"
				, "ATnPbHPk31dXd7mpYnemdAPZMfjnGcoH4K"
				, "ATNuDMCLkNVJKHvm844bgo1moZtvS5wXH3"
				, "AToiyNfSXLqjzRcSDRvRyDkMwELqYQXEcJ"
				, "AToVA2WFSVRBSThHkcmMU6ViTb21uqYhZr"
				, "ATPc5NCoYSbFF8vH24XmyEZToj1ydWiroZ"
				, "ATPCcWiC2mbbacnFbPcRTu9ms87fU1JoVf"
				, "ATPExRravJ7AFFRdbbJM7smeVYoExNUNxR"
				, "ATPWW3CiAMa6LYBY5mHsQnAuM6kL3CQ1LN"
				, "ATQ8GWx3TrcxqVz4HML7ghnTnKFuvzzkZ6"
				, "ATQbUzhrq1YW2WRLQCwPfq2n2BNXs6NTwW"
				, "ATQqpqduS1qv8vAVoguQJvXHEyz4fyPegC"
				, "ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6"
				, "ATqVs1BRcFwHdcXz7siWef4DwtV77nmvaE"
				, "ATQxLEnEJ1KGwygVM93dgAXSE54MPU92yQ"
				, "ATr3V3STaL2u17DLdQ3FKMuyRaTFoRv2EL"
				, "ATRAxn869eqTr4vp1fue2WG7UsjtC5wsQ1"
				, "ATrdcD7jvNDkzmYbYzyQZd6tJ9RCMzWVRp"
				, "ATre3U5LgPxeKcVf3N96PZgv49Gr7QCx2q"
				, "ATreU2FzZugbWRaZydS7KzX1Md6uTE6ryb"
				, "ATrF7B5GeJ5RpHkRdV5LH4q3j4SW6toEJL"
				, "ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ"
				, "ATrQF5Noc7bGWVbqSQBqrXSvb2sPQnMBNR"
				, "ATrQLc5iRBa7K77pmuoNEZER6rAt3Rsqc2"
				, "ATsBa1praf2Wsztf98hqdh9382XKZmZWzC"
				, "ATSMAqN1AtckjK9r7ER53kYbo5nSGBejNH"
				, "ATsmWnbrkwKs3TifrqNGwUbqmsJjmBgdFG"
				, "ATSPKUxaubZNM7WHmaLXyNmnTvkNVXV9Vv"
				, "ATSwV6HvvYikvLh6DRXcZGixJyst9nuf7Q"
				, "ATSZo9nvRW9AWPC2rWMJko8EkeCDUWCUiG"
				, "ATsZR6zB7o2oe3dSeY5ouoJY4jzX9TMmJL"
				, "ATT1B5myr7y1Ny4Xtv8SmryHdZHpVpc9yX"
				, "ATtDbTAvAPfi9AC6oyjBxEW7oiKHtBi5bL"
				, "ATtevDKyPMWMGCAi9P9LRZfnWKbUrmj3rA"
				, "ATTodY73bkgXggWaJ335ypwftdxKmyMgHb"
				, "ATu3iwb1VAJ74qQW5uYHxgoNUGsfzbqwHs"
				, "ATu5Eq8yNDiptnjnW3NdSHojhGWGKkzf2G"
				, "ATU5wRhqLMMhZ1etrK2wL7FjgWDVFg3NUt"
				, "ATUGoGA2KSMedStNPScBohioMfa7oLXDS6"
				, "ATULae4hoNSy2k3eMtsgd1k12sd7gTprM7"
				, "ATuNWMdv5x88BFiukhvD36myi5STtrE6go"
				, "ATuZVZfr8SAGSNFxmw7HhtBQeBdThPfnLc"
				, "ATV6jQy41ez5Q2ERo1bjVqZb4Bx6K4VYKK"
				, "ATvorHfgbYet39R6Bvc52c4mdygtJW3kb9"
				, "ATvsG6pHVGxUcBbYBBPbn32gS37e6qztBR"
				, "ATVt7msUnRqQGHWVmhx86nVojQVyjajZMc"
				, "ATvTiTrWNrqfosD7hSYuercfRru6DCEJiS"
				, "ATvtnwocwkzFmdCzYUJAhnLnpqz6YtZyft"
				, "ATw2EvtUz3VVDmrAEpX2SC5W7YFcNZ1fQi"
				, "ATW7wE1bhXrW5FbMFwrqLyJGjeWoG2DXJS"
				, "ATw9ngnB4XAt1xFyTS298SutvDrLiBAJF1"
				, "ATwGQ9Zq3CTpEV6G72VuvfxrXiqkcWrC3i"
				, "ATwjqJ1yKLswMxWMAgkePYsS5f1Dm3JTgD"
				, "ATWMueJeY4ZfwTjoeqtYtXq4gCYbeGzRvm"
				, "ATwVNESQV8seFC66zZvq1HSDbyr1h8cGmY"
				, "ATwx6gMzC1p2nGtVMnAWi49Ahxr4zLJ76b"
				, "ATWXEJq9kHzRZkrEkjy4BviHC2rpcx44T1"
				, "ATwzMqu473x3Ht1AdC5HmwVYh3A3w3RBpK"
				, "ATWZQGJoujJ8RyGXBWUg6DPzDpincsdrya"
				, "ATX2wNmavcT26DHaXYy7nsw9nxdw6tqbsy"
				, "ATX4gYWv4femzTaHdTuruDfzCQDqvGGKXC"
				, "ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW"
				, "ATXEyzgLQ6WhjpBBgdtKyKASPp93oogK8G"
				, "ATXo7XhGWXBAmzXzeB5S3qZN7oPKzH4tUW"
				, "ATxUPbWGX71b9vhTSVKbqchaiQ9eHAAxQt"
				, "ATyBd9H92MRdcbL16ac1Rb6AL62XenST2A"
				, "ATycywFh3iRLf4So4VV6XT8SftjFnVknaH"
				, "ATyQoDscQqu4fnnPeHL5hrESw7feqBQW5H"
				, "ATYtgzgndV6t8nFePXS4d4kqDUQ6MXx7t3"
				, "ATYXqR2VSy9R83YKTa2rDxmmwfNidTwTKV"
				, "ATYyvs9D4m9CN1NR8XDxEB8ozBUBwTjpqk"
				, "ATZ5LTeKSouRhGVHyHCvcd4epohuRgVvDA"
				, "ATz5PVtxCVmCf32nkxugPo82adwHb2KAaj"
				, "ATZbwyMV7kMf2DecPmCkojZ2YsT9LLLeEb"
				, "ATzckkjUjaqgBNFcPwanfNHbdM93dTF7BG"
				, "ATzCpYEywK9XtA8QeEDG9rqff1cxmGCYTS"
				, "ATzgBdgi6gwFEcN3652j4DiogPibAGSvrJ"
				, "AU2hiefMWZ59tvKk5KJY4UoVsHdKkDAfgU"
				, "AU3joSEALWGtTvkBPKNDMZKomMj1yC5fjc"
				, "AU3pY4z9UnZXg2oKzf5vqezh19fxmnas38"
				, "AU4SUmcmWrz6ttbBqjFNg8mmQMs9QB3S97"
				, "AU5bGK7JBaie42HKWjMzCNnmLLZBtbesUT"
				, "AU5DaKZbSZGF8ad1MuVP7AMZhr7Y3kHZTs"
				, "AU5fcr69FGVrxp8cY41ACs2HV4PZfQxsnV"
				, "AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC"
				, "AU5hKxL6dGuNMqEJmQkS7srRsWyoP31tSc"
				, "AU6cw2bML1GQnqEvpexdRPb6RhWzVk1Bzw"
				, "AU6i3dun9QHLNzaXXS74c2y9LyNjhtuad3"
				, "AU7uEZYkkLGBNjrGtabMVFkheMXxZyRbQG"
				, "AU7XbSrg5URCoRGimSv3DgfUb4dk4zJSar"
				, "AU7ykdsjGkHR2C7U61MUWtWweFNT33Hmc8"
				, "AU7ZpvvNcg9US51AYficNY3MnNVHV7t8xd"
				, "AU82iEXUbyTRKbWq9ZWkaDbSJHSCcCbqNi"
				, "AU87kSM4xLBx2yT3PhvyQaPocHec4ghcwR"
				, "AU8nTbqkBuAmzi769nLYjkfteKru5mKmxY"
				, "AU8ocMRxGCYE6FhMUsyXRXvUuc3sisMFKh"
				, "AU8oLFXEmWHMauvVWWzHdSMiYJ6zpm2DiR"
				, "AU8smBKbVDMUBMLvGcYHiEauKXttzXieyZ"
				, "AU993km9qYLo1nngubywtNEwvBG5iVQGZU"
				, "AU9FzMeHddK6vpsTpXBysYB4mDBoMrKwzh"
				, "AUA44fjABrfRKi1QgrwSXy37R9Vv3JRQTo"
				, "AUA9H3gpnBKz6iF8YD9Vkfz5xeNdnsGKHo"
				, "AUAtTpU1rYwBv76dvpLhHHVBdT5FfrgUSu"
				, "AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic"
				, "AUb3uZ89Y1izKe3uktBoxtWnHFT1y6ajfp"
				, "AUbES6tbzdJNsEsZTZy1bp3GyYpViFsaf9"
				, "AUbiAqHEDTX23QqDd9WBXw1qXkXr6ooQwm"
				, "AUbirw6vrVtSejHdYMnTBszM7uFSsQuh3G"
				, "AUbjxdJGh9xcH5H2pmcA3Y1wejfBBe2n6Y"
				, "AUBJXjNmTc1Nf1nJTCeqwgpkXwGxb7xPdv"
				, "AUBxfD8Sdo7uuy2e2YZnycc72agqBSH3jU"
				, "AUc8eirJc8eUCXLf8LC8Bujhq6RjbPTE4C"
				, "AUC9BqC4JfUqbPsgSp4MMnyT5w8FgB5Apt"
				, "AUcDrFmDUymGxJe2j6RsffFcUhvtfg9pbs"
				, "AUCJP9ZrXZm28ETgBkJ1E3hqhYudiFiWt7"
				, "AUcMx5u3LkhWnoGwqM7nB5hzRsW1aMhCHe"
				, "AUcujm5sCBX1rVq5Kk9RJR2NxLWTB2mwZc"
				, "AUcwFcZv1LAaV95YtGxT1zy55gVCLUVYqj"
				, "AUcYpLzKyqkV9ReSezzrGUWmXauHstLLKj"
				, "AUD3P2v2iQ1dVUwETyTwmyCamzXyLsubfc"
				, "AUd5TL4xY6aPJQTpUbvTDt9wihk8g2LiZz"
				, "AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa"
				, "AUdESHwnpvcH2kXmgW1buX853HhKA2waA5"
				, "AUDiagWp3xG5zYvJSjJ8Bcg4ErtLzxtb5R"
				, "AUDubWGgNbnDQe67VfSTt1U9VnqWGQ29de"
				, "AUdviCmr2XyddivPijPahQ33rRHsAffcyY"
				, "AUdvkiT2KK2dH8RbQfiP7haQ4gxEqB6MXY"
				, "AUe1w43fRyGPS5yyKEsuDzGjA92zggakFx"
				, "AUe7xjpGPupJhqgv9X8Pu564PspgEfPCUh"
				, "AUeaiLEMeRXsGYGDz9b1qxx56NjTgmKTzH"
				, "AUEb6oWQ7FNMM6ZhGVC7ogkbwBjRYu1RG7"
				, "AUegGUMncG3wAxpgmHizzYZFuTebWhmAYN"
				, "AUeSMM9jELYPY9kbxfU3f2jRUYDD2jNiqN"
				, "AUeSqmUN41DAFZqK62XMHrsYQR35e7Xvwy"
				, "AUEZCtFiooGKUsrMQDAfDWqi8YkqVsRnPY"
				, "AUF6UYk1N256ioBUhiwCc86ZCH6bSASQg1"
				, "AUFbxNcv9jLb6gLbt62y7VzHbhVmnjhFQX"
				, "AUfiKUNE8FnQF4eYQK8nhmrFwW6u1DTag6"
				, "AUfQEvv6xQ8kTWFx7rj5ZWnb16Xn5gmuup"
				, "AUFRQY7nYTyisLuuuWFzb39hUNcpULaAiR"
				, "AUFWTXbQufvnYqHPvCtqDa3HtwJHyY3LLA"
				, "AUg9mfo9YDNUqDAR5bqZWqshCLoszpTRYP"
				, "AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB"
				, "AUGfQFqe22yfbDyzSuyad6cAZtkr9PnhEw"
				, "AUGkjHFnnrC7aWnHcNjNivfscmSNuNLKw2"
				, "AUGpzuHtLNkUNr8mNmPfEGqRdMewnbMiJc"
				, "AUGSMdnwptXs841HySvMoyoQB8XU8a6Huo"
				, "AUGX3RWdZxegJW5KEerPHCm65cC1Bzxud8"
				, "AUGXp4HUssWY3QNUcZrn7jswYiX4X77syv"
				, "AUGYpEA27yhy25gyaWiSpTtAsB35tvDYic"
				, "AUgZMv2wJRw5a9tmaphpSc1q6bsZsW2MLL"
				, "AUHaUPWPh4v8Hc5fAPMJTk2rJotoSsmb3F"
				, "AUHDApySowWbFY5Km1QDN1ScENX37yWFBQ"
				, "AUhFSQS3a1snyjbhRnxTEDaVxRWBDTJg8k"
				, "AUhLdTtbTiQjqAQACrmfUpktuPJVFMydax"
				, "AUhSvaD9wfAb4ymTGfk6JSRX1SP16SHrjZ"
				, "AUHzt6kCEsL6eGLbdzunZcnW71SHt8mTVD"
				, "AUi9R8YQnxGPWVDbfukh5L7fpJ83CoM8dz"
				, "AUieCx2f8i4wHQLAwcrD8TZaYBHbhhBESS"
				, "AUiLJYwV54ShA69oous7NXx1BuoqyBCGnv"
				, "AUiX1DjRzqhQ8MK4ELD8bHuMMoLHf6v99i"
				, "AUj1k4dqrw224FaW9Wj8ZWCaYXapYoQzgT"
				, "AUjGrMa7sTH1i6nwCt8r8peDimLd2oFXWb"
				, "AUji8PNQj7Abr7sTaUikba81GLupKKP2ii"
				, "AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x"
				, "AUjsT1ya8QBjaZHze1bj6MttUQndnZ1eCw"
				, "AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep"
				, "AUJTviCTRZnZfBpYP595QoH9RqEDCK48sK"
				, "AUjVsKwBQNRgSQ7FbHsoM74Dc7XEnAnRWL"
				, "AUkCc9E9uvAY8wbPcohxZKpjCdRpD4nESz"
				, "AUkRxEuN6e4QGsqJ6ePTc9RbGTYmQJcfwV"
				, "AUKSUsoyrVo84wPcyfU3ZUKQKny49Dvwzs"
				, "AUKUmkRaNUvjQrrbobgfmM5sQLen1aZetP"
				, "AUKVAZHvrbHMxL6VA5qAny6XcEw1knPvXQ"
				, "AUL6ADJbotRiN1qKxTYYgyiHjaTumJbw9Y"
				, "AULeZPHPEr5kiZfH8TeGpDc6XZxL3N9CFj"
				, "AULJrtE7F3pp5MSM2cH8PkrxKsT8XafEFw"
				, "AULmN2hjpkxJhV7fM7iuFm8YP4oKCLBJMw"
				, "AULtdWhwnRgkXFgiQURjzEy7VKnhwfy3B2"
				, "AULwLGMeXRuZKBuxMtPU8uHH3Qvq2V4KDQ"
				, "AULZVMBEeunHcHWLjzAxr3a2NLmqsbMBMv"
				, "AUm3gcbEDuxasHNDo5CDq3fqiXbwGFwfqW"
				, "AUmaBWZ6pS22ZVKTMgwZECL2Qp9sqVAvWn"
				, "AUmBeNen69o8iGnHM2o3XZXbanv6tqzCy7"
				, "AUmeCCTw5AmKqmmGJJxgdbQY6JiZVwsW3a"
				, "AUMt125gJ54jE5PTkkY7c9Y3nVW1f33WqF"
				, "AUN5V366mgYpygVrdDxNSPszEG4RtQNyP7"
				, "AUN7e6XurUgHBxWFrx4LodCuxpKgAcRafC"
				, "AUn9Tid7nMF3SJKpJQcTUFZZ11VxkSC7c6"
				, "AUNCDFQVSW5YQvLEcc4tTYgsiqHV2cZiDC"
				, "AUnDRdw4Z9vPuX4jXiU7EACfbGWXxBFbnz"
				, "AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw"
				, "AUNg5fJzjEyzcGc3NT5sr8uyVqYZQe9NMV"
				, "AUnm3dkpdxdDKZUnnVaD346pUibB1Q3Yq2"
				, "AUNMhfNG78DqNR67uMoNA12ZBFJGb7NE6h"
				, "AUnNGFdSPfWC1avR2ZQUvof2gkhu2fHJ35"
				, "AUnQEW1WWBwFEq14tekjhqJ2KGvWZjv8Ee"
				, "AUnVouL3CcX636mxsM7nQiZ31NmRqMfF5S"
				, "AUocJmSuUSSEoj1xJpTTjEeh1k6xdL7b7W"
				, "AUpETg2dS2mfhg3vF3zDNZfSE7SsU3sXba"
				, "AUpNoY39NaL3aMDepZDuTVhPCUf7drtTVU"
				, "AUq8YshD5dvpbZepU2uBf8VXxU66KeHQSM"
				, "AUQXAqKDeQbfUoBxVtw8UqQVQbB8zbSDhX"
				, "AUR9aD6anKc1wtNCYPmK7697oaiABhZ7ZW"
				, "AURCbabmQxd84tn7iDvJaLytm2HQKaSyzP"
				, "AUrjQsNdVoejQwHjTu5uT2bVsTDTuPmTjT"
				, "AUrwicDcEuaN9Zg3WQteEK68nxzXAcuHzF"
				, "AUS3ghWir9KLquh9KSyyGGQzqg3bgZARPk"
				, "AUSaLF79SJL87V89b1AWLkT8DPgyRcBQiE"
				, "AUsMwKn67HXS5CeCzm2G5WbiRfmoAdD92G"
				, "AUt2qzdYrw3PpKmLcxH3vzkgSSqT1S2LsN"
				, "AUt3MGDrrcc7cWUK1jZArbLVtXJHDUk5Jv"
				, "AUT4xLxPZNBND8TP2FPzFxgWxVxd4W7GJr"
				, "AUTAUUiYdyHDZAPKyjAUThq8TsWzRurEk4"
				, "AUTCLgXYKGt42j2ek915GQfArBxXi53e3g"
				, "AUtDnN8sbHdxSJ9CFvPU3MRwoH2PhgyYg9"
				, "AUTfnPwx86MTbAQkQszztFnkvTyXDRWKYc"
				, "AUTHeBFnGF3r16sTaKjhNfEot2eu6qBACc"
				, "AUTJ6DjnSe7JYDEfFf4RJ4JwZ72FsbWHH4"
				, "AUtKDcK1fcvfMoWoAEyG3VNFngs8FPo2QH"
				, "AUtkk2d8nhmFPs6kocczBjzgGpYxTvV3C4"
				, "AUtsYGk4cKrBpYCSF4vqaB7UPe2gFN1vvE"
				, "AUTybPr7nFvybHGjaDSLHboVaHFhrvFgjN"
				, "AUu7wDvSigA3jtLV8nHov6LBPKymhXcYPE"
				, "AUuhG4vZgHyLEvXReiKhdQaY2f1WXHVJRw"
				, "AUUkQA9FgZd4EYxL77L2egFxCWkk3xafGt"
				, "AUUvSu8ATuoLnDT3rShBLz6Pe13hrLPfLU"
				, "AUV18ttusqtLwu4HLQ6BpFrDUBnQbxhQA5"
				, "AUvabRbcxFLKaC4xpZchhZ3KWHFC7Dqvu6"
				, "AUVCJrQX51CnFQuigJ9RK5dxwEmHgrABTq"
				, "AUvLQjL7GRVZSgiov5Wqbjmd8eMoQZr1Ex"
				, "AUVNg586VuvoC142FvKG4iteuL7aCikViA"
				, "AUVVdCzb3BBrHU6Z83kkzA32vT6VexwJ42"
				, "AUw7Dtbn1Gb91aDaMEHxraWffw7Mu9HV81"
				, "AUw7UWFT2UG89gddRnvXRcyXMF4Riz37MH"
				, "AUW9hhGKPQ427SxmVAnUgRbbeuFFuMdKdp"
				, "AUwaiRAeGM8DR2aRDrcTkn6r9mwUo1kebv"
				, "AUWtU3ssWWvwphujTXqbJXuZkWKnhEou6a"
				, "AUwZuZ8QSfuDh374AKTdpT9QjAnJd4w3Mq"
				, "AUXi3fAj8rgch73heFz1moF76F8QaukjnZ"
				, "AUXjv5vUZK3S2ZRkkj57aW8e49Bpa9acex"
				, "AUXNe69CjX5DFmaAzHxwY18KTXUKyidtT8"
				, "AUxoebu8XkYqkNHkGfWB13MYUE2VTN5keC"
				, "AUY3JeAyXy6pmGWb6SFNwHKd1vT659An25"
				, "AUY57jPSCK47EUeBcyZKxCGwvErLxgDMDY"
				, "AUy6j79yVcyRDt2eorX5pwTVAvJCMMexTj"
				, "AUy9L2bT7if7kxyu91Xeqe7ELUyc28w4RZ"
				, "AUYowzYa1mUe6XyCHZ8PXF7vnA8ehEYKmE"
				, "AUyQ6soEmEX1CsccPrijSNQMZcUuQ4MR7e"
				, "AUyS5vdbjojS89HisvLgxnDiXFqt91uiYX"
				, "AUYxUk5t8jQajkiCgsfS9y2JKV4Tu81grP"
				, "AUZ4tMf6igTUwHvCHWfZ82iNTXhN3rSpYy"
				, "AUzCAy91KriZis7Z47c9Zoi4i6m1Vg3Ems"
				, "AUzhtctuBBWmq6ef34dRVuWVBGRYr3Njvi"
				, "AUzMsL6x6J1gUGXYWX14jdxphBYAdtNDFR"
				, "AV14eghaL1tjehSZcVhSbpJoxL3Lhv8ugb"
				, "AV1GUyQqcnHLohqJ4AeuLii4zon3mUEekB"
				, "AV1SBxDiRztKU512jK95UuXy6rjhEBbTd1"
				, "AV2EUmsuV3xwGcAw2J1G44PYHZTiUHJnZY"
				, "AV2fdvzRKwvfs1wpiTGGSVEx61BdL7vmVe"
				, "AV2JgGDmd7tBkeuaoyGuuscS7H6yxWKfaf"
				, "AV2X4zpQ8GG3pGiEb5swQfzgctAhLGXRf5"
				, "AV37eZkBJx7D1b3aftjme7kza1H5SKRgTW"
				, "AV3J6HSrmYj4Frh61sdUU2PRiMjBmTyA36"
				, "AV4c5oGn5nCr8chEhC7XWB2oJcV3szN5jD"
				, "AV4GsxTA6ZUvVvbdSa3rttrJxwheGdNCrY"
				, "AV4tCvQjaPRPCnRtmwgptqi6WsXGE5fqRT"
				, "AV4Xcq2vGDABR2XUX6xFVeG5UcZNoSMFFi"
				, "AV5ApaNyza7VLGn4shgrJaomFFBfkxj6dY"
				, "AV5eH9pprbVS5EbJVo2J9fo6X5BZX2KY11"
				, "AV5fti3h9fmNEUPuTmZ4ZbzGn7ipNRjxZY"
				, "AV5ThdmUKjSjNQw9LWxHxZ3Uk7tMcyUu75"
				, "AV5w2GmfqCFTzk1E8SQcWWdrbgMFVyf8jr"
				, "AV66987H7ZWAfAcBU6yFKEVo2KwSKf4QcK"
				, "AV6bqUmNoe8j8C2twEHkJYUC2s2TxcdTgQ"
				, "AV6ELhWoLN1pYA6HTwnh6cPKDuz7aK18uW"
				, "AV6GkdmvRgk9u93n5MiZbnVEcDpSz8EgJG"
				, "AV6jhtVBA76QF2ZHouzg3bRuGPamLRnesQ"
				, "AV79qM1mK92dpa4c2fWqVJ45E7DurgbK2S"
				, "AV7FoNTDYBknS2UgvdS5B4gHtAv7aZjcSM"
				, "AV7H5pzKJoUR8pQD45YTT8kFg8bbuvxTGY"
				, "AV7WaxUhw5yk25zwQgrRaAQjLo99badtaX"
				, "AV88UQmrxLbDy7KxLHPJrSgUrn89NAiqPd"
				, "AV8qNNcCmpWkQ7eSNKYLw6M5ovDXwETwyW"
				, "AV8Tgo33DPzCny5e8iKU5QmqrqpT6TMHJC"
				, "AV91mmaqqAukUZ3Zcjbr7gpgCk31vvEzo9"
				, "AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4"
				, "AV9wm5P1bZU5Mvnsq8gDSnyGFUniVeP8bm"
				, "AVaEEEV3Lr2pNCVwiEV1ar8AuNya13LzKz"
				, "AVakdgQhFkypiiUmZ8optVAdwQWWPU2n5q"
				, "AVaMy3Z58V6fZN9NbeSHmL53xGPUfKBqMF"
				, "AVawbqq3BrBaunZBjPqNZ38sznwYBuPbj9"
				, "AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb"
				, "AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ"
				, "AVbdWoTJJ9gudwb1B9Lg72SR1NSyFzPUDa"
				, "AVbidq8WYKvP4PX3Kx1KoKuHFZR27SUzud"
				, "AVBizDB8cmRws4jiphJGABbjWj5piB1Sry"
				, "AVbLDZzXPzVR5H1UKVkr6S9bPYtQ8w2smw"
				, "AVbPU1MiF1V1GJ4BdfzAkngHWmKDsXa4cA"
				, "AVBuCdmgK5vAJCgUzEFLiRLEfzNpkuhQuC"
				, "AVbYxJU3ZnmtXi8Cvk4uVpn7jt99mKZgW2"
				, "AVbZdp8NL81UGCP66veJWBY6BUFrS3c9Yw"
				, "AVc6pBgUBnRzZBoNGnBJ4W2yPYkaoWwYbf"
				, "AVC9ui8zUjuqeWQSdGfehS8G7hrECN3s37"
				, "AVccu9jMoqp8wgfGSwzoAtwVwkNRWyePMa"
				, "AVcncAgMo9E8bo8StPncmgL6cXjnugrmGu"
				, "AVCyH3EL2q8EcSfRzWqdKMKTBvpU4gRkjQ"
				, "AVDg6zYvGXUHM7PcUieNUgsiT6pDsogss6"
				, "AVdJBoHK4YCkdJiUj6FsJfiezi66QP3XwX"
				, "AVDLvFw75Yn6n99HbEv7Cvx74ubEZJDZ63"
				, "AVdoDthVcvrRdaKtm4Y1M8DCYXuLtdes85"
				, "AVDSknZJQ9kuD1krQJQYzshYXFHtapMoDe"
				, "AVduACxZbKQDgf1ZvQErvYPFR3eoYKXDjj"
				, "AVDxwKh89NzCmG8Qv6xXVR1a5jLFAFUbMV"
				, "AVEepoNmdsSq6hNfuC1R34ryvQemheDWBv"
				, "AVEUY5itLBC6TvwdkqMzRYdQxDHqpBP8WN"
				, "AVeXLS9kCW4w2WcS6oKxTRky1cwcFsyyds"
				, "AVF7eiLRaX48VXuNWRzC9NmT2TCxMKuvoS"
				, "AVfcNkMuQ7Z5ebGQCSjdngr9cYXoWkw5ZG"
				, "AVfJw2VJNRW2E9YNXCwwaaM6LQPtMnosQQ"
				, "AVFkyvwqdMuJnTUygFJjKVBfoHMBTuKU81"
				, "AVFs4j1v8VbkvdBJSXx7kGW9htJohos2nm"
				, "AVfXYbzhF1Wn4QA5EPR3UXUTvMoWB5HjUn"
				, "AVFzXtYMDmmcUDLpaEEV7poCiyicqK3uqV"
				, "AVGAttef6eL41ZMeu1fMMtDTQgWrkDhaBk"
				, "AVgjun2WuVr8V8x2Nr9PVt6MEeJLfKiad8"
				, "AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC"
				, "AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1"
				, "AVH2FJP6EF9SYZXtEekUPXSFehY6WwQHzR"
				, "AVh6vPCghiq346RLqrEJWxXDR3hWMVGbVP"
				, "AVhbAqrThVkugpQb9jzc7XmxzQEnVS5PJ9"
				, "AVHmFVDvodxngShqy5sjZ4Xwz2R1J3JJo2"
				, "AVHP87ueAgRuHZwJ7ygeR61KNcb9zj9QNS"
				, "AVhrhkzVcJzZCvTNEuDT8mzp2cRUEXhs4w"
				, "AViAAJWCV7tjk6fdYZguqcQfg4L8t173uY"
				, "AVirQZzWfY1gwmqR9rZKuieuoZW9kAyeAH"
				, "AVJ6KUcJjnm39fmRwLD8gYnUPBLTxkoDBU"
				, "AVJ6WBRSVWfjtrFjF2qiBge88xVHVYs2hj"
				, "AVJ8dvekswxK27t8Y3Jb2GKPKRSVkvnyrk"
				, "AVjAaVmaqQPQWRZn4cCiAwDEmAtQsxahJg"
				, "AVjP15iAvZCnBdrN2fXaBwXPyGW7WQnTPp"
				, "AVJPusv9NLLN1VeDGjsssjgYZ1MNBAxiXW"
				, "AVjQtUPXVG83qquHYJrKoTz5sL2WHVh5JP"
				, "AVJsWrqtkhnQfwBLeMp5hGf8VFbyJ7usgf"
				, "AVjtAtMWHx8fDDSEvdM71sy2F8jPgSST5F"
				, "AVJwXkVVBgM2oTL6DXEEgqgdpk8E9voCwF"
				, "AVKacSC5PFDi8u8CHv9qrkveXUXCSJNteo"
				, "AVKGmsr4eqHMkbsj3bPnNgMjci8hN94VaU"
				, "AVKLXzbG3Rf2TbuJVja7kbaXe2CaLHXTQe"
				, "AVKmFL5E2mwXwffaMoQDhDrCG7TyJCgTms"
				, "AVKnWdekrBdnFUKykskNLxuLrHdhA7QLTu"
				, "AVkv3Ej6qn9qPbctyU5PBJUtYpTgspfPWs"
				, "AVLK4hNFkFamhUDEXUePnHefafCxLViz9L"
				, "AVLm26GoAHdQEjXcSL85wuzdVHZXafXyXa"
				, "AVmede9FEeUsmt3W8n7sDibhEkRQMYSBpY"
				, "AVmjFAbNsa6wjWByUJ8Wap4Y4ivk8H6zqF"
				, "AVMMN7CRa5qTTxMLueXyxLvAaD9vFX3idA"
				, "AVmniGqTbaiTTA9V7moWpmfV3EVsuyQcBh"
				, "AVMvtMsjWsNoquXDg4jPh2RZ6S4EtJyTrn"
				, "AVMvXS9dwWXJjm4RGMfJcpPqmF7cUKDUJB"
				, "AVmzYwR7s1ppC8pMFdv2UqZ3Sxfs52idxy"
				, "AVn3QRGp23Px1e2eei8Jm5tfpzUXSLk9ha"
				, "AVnDFhJ9hyjnbdeG3tnaBMGRgNH7Jnx3LL"
				, "AVnJ8usUtBcC2dkq4ifm362bxiGdiXcnhS"
				, "AVNkL8ySDQspfwUR6CFKmscx3hMJYbE3fD"
				, "AVnmw4tBc4CLLBPD5rc162MbGTGez6gATt"
				, "AVNPFc1eQfG1M2X12cWsnpnshztwmusCV9"
				, "AVNpjrcN2pj8XoeWFgzZEToZc3NZinR7Pa"
				, "AVNTFmhkQgopXAWAyGz688BMN4SoTzrgwe"
				, "AVofTpJcjZVr7K9VzQDR91rRUaoWoEjoU6"
				, "AVoMFXyYWwJH33ZT3xMEHvkNbqk9yWnbu9"
				, "AVPdV8BDgzQDhTPoKCgkHEgdM4sfBeQYpg"
				, "AVpFyZZdu45Td4mwxS4cPZm6Ess1HygsUG"
				, "AVpGn36orCi42W2mHMrsAPs3La1R77HXDJ"
				, "AVpK8dnNk3rt7tAzah9gbrA5Rf2PP35BF7"
				, "AVpqKjs3ASq9q7hB5CJXZfFTHHVcGiN9rC"
				, "AVpSeDS4dV3UCTHC3aYqDyjwJGZYLaAdjm"
				, "AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX"
				, "AVq1RdRox1NZaowWyoGu6AjnebMUD7FGrt"
				, "AVq24DhkMk1pP2fcPheeoPfVS819wFFTqF"
				, "AVq5zfYeLkH7egUXBPR3YAtJ75WnzQhK43"
				, "AVqAsN1Ggxnh8iSVyFywnSRkhHDqZbiBw3"
				, "AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj"
				, "AVQUdvE83qfNxZTvWqmG842zofYHmAQzkE"
				, "AVRcd6XjC2HT72h2A6mqJTBV4Z3ioSVaj7"
				, "AVrceFsjKL61e9GrM1Yjuy6KytYrsPuYCC"
				, "AVRhhYtrR4wpWkEw8X1xhGvRhPX7eqK51f"
				, "AVRNqi1tWd6QW3VKkYjn9V12s1CwE5otCJ"
				, "AVRokSQLk8bgvPwUDbYt6p8xvZrSBAznoT"
				, "AVrpbuMoFvf9XQJL8bTQEGbFYoP138XjdT"
				, "AVrpnQnKp58hrkVmcTiUz1475HjTPeUynf"
				, "AVRPUqpUa9QioNxiL1saYFHx94dx17Hkra"
				, "AVRtQ6ErQFHZZvsTSjVJ4CbJ1BzdkDUmaY"
				, "AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv"
				, "AVRxf2qxDkSAF7ho5gjEzn6a5HyLb7EG3k"
				, "AVS6822WdZ3DT35Vp66RPqNYtEXFKPBFFo"
				, "AVsb96Mb7RCPW6EN5T8mAxzZWC7rSgh6S8"
				, "AVSQ1bNZsAvuWwm3ZArR9z1VpSbmtJpprA"
				, "AVswKjKpBHbqhQvkUNUgnKFvX8ysbk3nvy"
				, "AVSWv56NZeW5pchhm6MuZyJwTxDyqwhp3N"
				, "AVt15fH21QcDkpkf75pmmoebenjhXu8om2"
				, "AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1"
				, "AVTBvMx5YajTtPgeWT9Be9j7kUadsoQ5rH"
				, "AVTGZ9LirQZen1skN6qUi6ajwapqz5CKEe"
				, "AVTqH3FMkj3UMHXMRahJqRPcDyMY4c5z8N"
				, "AVTS9McNsxD1ddih2Q45WUGHQmbKtYfCis"
				, "AVu3j8n5HfG6bS1yQx9LQ4tYknV4T6PbK2"
				, "AVukUHB8UL4MHJrrhU3nUX6aJwaDpFag4f"
				, "AVupWjJzM9LML9XzcMLEhyrJX7rpCqtaV2"
				, "AVuSfPpMDzFbn3HNAEhRrYyLCzqNW1Rydw"
				, "AVuTwsVmTuoi52YNLHR6zkADzemPZFgWFt"
				, "AVuvQE5EzBnKhpnBRh4Gs85U79nCmH7375"
				, "AVuwYonWaiD1ZA2oLpcYMz37AG9b6eLqDV"
				, "AVUxDBVadzHNDETe8MW3yAwLnk6m4ahfWM"
				, "AVVhgD6JQhWJ1PTTc2hZqtg3TVocmeQxno"
				, "AVVwo5oTJj2gDEmgLHAGorE6agXyrUU1LK"
				, "AVwAVqP6ji7TsBaXrZuA4YUraZ6WmrPqdh"
				, "AVWdptxpZj3i51TdL1Znyut4oWBSWpucLa"
				, "AVWEtsbWb1TbmcFMvubAju72eRnhdLxr77"
				, "AVWkTbjdRQqD8pbkYdLiFceDCB4eNqRWn8"
				, "AVwom6z4Nu4HTVVwzPRiW91AaSGR7FDbDF"
				, "AVXaora2ZrjaCzu48V2PhPTVhHEZY93ePa"
				, "AVXH7ZP3FsPX9VywGwbSfxsiufnCCZBwKt"
				, "AVY4mqajjL78AaudV3UiVZxbrxn7EXmhWw"
				, "AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG"
				, "AVyQpAdx8R7TzxRd1sBgaYmQvBTUtH1rqb"
				, "AVZaoRK81UC2QxXiUTk5ixziQRseLiJWdc"
				, "AVZAXk4nNb1oCtj7N7Ldruop82XjRrXe9a"
				, "AVzGPrsB3DmDNmqnenfw73Tw4F5amGwJu1"
				, "AVzkDtu9pTpj83abhDFZnTpMEaHqhnsyTW"
				, "AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy"
				, "AW2k2SkUMTDUvNgCYbgaZ5zXhpjfAw4wwh"
				, "AW2oGuwn9a2rYD3TRWieyKxqa3mWP9Eu3r"
				, "AW2VjumrBEUyG8JT1GjpBbd6Abir1T82P2"
				, "AW3RFUVB8xRgC2VhzzYDrChYBdkW8HHX5z"
				, "AW3swgPow4JC8QJQngCJyzVRWYyu8twyaa"
				, "AW4cMrp8YVNoVV76DK3XH6GnUUqoPSiMWW"
				, "AW4Dy2dZXvDhm4MPmQKYvziLqHdXHyyauM"
				, "AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH"
				, "AW4tNJV5xjPDzy3iKHkAZBoegZG1ARc6SP"
				, "AW4uQSYFQg13dBVzpqgRymkYTUyv3iCqAA"
				, "AW4ZpTMGD7aMVj8ztGwA3nQHHxYL2Zj1DQ"
				, "AW55hmDN9wnyH5ztTa73iwg3BMV1g5BB3a"
				, "AW57Xu9BmzkWpTCk5eQAeCXBHv9YVE7MBF"
				, "AW5HubfLMvdvZTG9yLawerN5a2Pt7t6BXZ"
				, "AW6bB3s3GnJmf9G4RDXtTYSatGyohZKxYF"
				, "AW6bZMmsdKQ4g5FgjjzCDFsC4LohcTEwyi"
				, "AW6zeMNqYjN69rgRqvnPaWY5HgBavijxzE"
				, "AW72CAmak6MTZLjYtHALqNYRWJNR1zmfU1"
				, "AW781kNqCPJz8hsG8pYZvXZcamVyySjFjM"
				, "AW7kkKTvixZhm8XEgvDZQkgsm6mWTnoxpp"
				, "AW7vs86tjzx3bGd6Dno8kzKEAsJc2jEeLc"
				, "AW831CYqEMZF1xLM88o15YS1ukSe6w6u8B"
				, "AW8s8WUbPyxNAiV9M4YKyXAYHEXUgWuNW6"
				, "AW8uC2DkeFymVJiGR2nVKjj4aw6NyTMrLt"
				, "AW8uQWRgavkJP5BndMDetJBSrB6ujuQXUQ"
				, "AW8xSyHcHWZ4bGwSVQ5hQYejJf6CUbvpav"
				, "AW9bZ5AkSuswvCCHFBJJHXW3LZgi5ck7D5"
				, "AW9FjMpcC19euzKnKHCnTEKrc91FSB66kT"
				, "AW9pm7xBngHL8AhRy6eB32q91BT5Q2JZjT"
				, "AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH"
				, "AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d"
				, "AWannKuWjb4f4BK7AZaAHUXzMVfNiENaTW"
				, "AWaQi9AxSX9v1XSDyhygWAYETgs4b4xU1i"
				, "AWaXM3RmG4RgoYfPcA6umtH3ybY8DbYCmD"
				, "AWBESnkx7ujDL3F7ZguJRQzBRzV7EGJ6G6"
				, "AWbhdYecxRxvMbvYfHcogmH9cvmBf9FGZy"
				, "AWBjF5375dx4qwPFvP7uSMVvjwkmeqSCj8"
				, "AWbrH8xUqXYZMGMhB7YysMTCvFhHWvnxnT"
				, "AWBuqnmLYQ4QCgz5xfjxFNsmRr5i5aXnpc"
				, "AWByE1yqRSCnws2oDoxB6DwcznvjkU8qhC"
				, "AWbYJ1bbQJRC3B8CbBZ62g5mcV7uYP8PCz"
				, "AWCBpx4KkbNrVoytLJQ5KjCGK5pgCZu4dW"
				, "AWcc2zmbCJ6S1RTX8HJotaD6WGiFe8uWaJ"
				, "AWCH3A3oDuKHD2MM6Un6LoMv52bwkpfkgg"
				, "AWChP11HBFJxKT74drWiMAddBumAxfRaja"
				, "AWChQmxrHHLc81x2bmBBQPVSPkyp1dWjKo"
				, "AWCHThzAq4Z4xWMBcAfP9W9q27hmCYeCVb"
				, "AWCiFVwo4A6iRt282VsqdRkky7fJeQwHLw"
				, "AWCth7HzfHgBuCZsU43BfKKNdRQ7vWHnF3"
				, "AWcUHZHJnQeeozc1m5sCANrGMwB1HUZmcT"
				, "AWdfCd81BhjsQ6u5HTKbhabkgGuqpNF8gC"
				, "AWDGstph7rB9f52cC1SDiTqw1SYtT7TQkk"
				, "AWDNsMCCrWGuPcS5XBTLG8cUvVXQwSUKax"
				, "AWDowQkLz9srAFDaf4yh3moF2Xeedgbb5R"
				, "AWdYKmzNKBazrBZ9iHKB95L1i7dg642tTp"
				, "AWecrxwNbskTSopQw91V5ybkVVHK6F4axP"
				, "AWEDgxL4z5AHuMpGW6DyeBj2B7QbuYHywi"
				, "AWeMGt4SMJAhA9Wi9oqunEYjUbAsMrUEuN"
				, "AWEmHGXvWaQAm8RL5qxPFDrNZ598XjzZVX"
				, "AWeNSFjGo75J8HrRpJYDY44AUSkcwpxCgS"
				, "AWEnTHg6UFEFz6qa8nWDGxiNsdETEdfW9L"
				, "AWEPTueuTYYPnqH2b5Je77xz34PkhXfsd3"
				, "AWEyqgXYGjQQRH8doTFXM2ZguZgJpRhsKd"
				, "AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y"
				, "AWfgQMbdCeCQmG5eBBBxQtNMw7AToe9XAv"
				, "AWFh7AJ9agfCKXGLKLNzWuPbrmF9aYWNvc"
				, "AWFjbbsRTJoe1q5v6nCWnpk1qpP3bS3Q2X"
				, "AWfMy4iuUu9xFmxguQ1RMXPxMrco8R3ys3"
				, "AWfNDWwNMg5RmpLFhLaSf7n7R4TzMFcMB8"
				, "AWFoJ7taanmso5yNH1QTFsYnTFaJsHPvEs"
				, "AWfQVtysjwAmEtkeyFTwwkBCqwNygajmob"
				, "AWfsyC5m1xxUQYhSuzKEktQJHRjqRnwUH1"
				, "AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6"
				, "AWg1EhR5vaMJAbzyZCbzWcBox3FFoqnJ9V"
				, "AWG3CRxLseZ36UeBe5JBgWuMd4NmhLDZi3"
				, "AWGCiNAujoMshAQkBWS5MePkB3Kc5zT3FT"
				, "AWGJu1hLa9oMUH5JWt3HzkFQvL8ZXKRgZa"
				, "AWgLgWZtadjtxyJj6KcTiKDgyy2J5xpoWK"
				, "AWgrqMu52mLLr7YvQDvS65h2uRYMsyKNzv"
				, "AWHgrHZ7U57adUenXH8T8MYGS15MXGUbv1"
				, "AWHhGXSCXSZf3ycRyQc1MGh12eQJV43UK9"
				, "AWhPsDMhycUpo7PGtaJwzZhcLZWugiKaLf"
				, "AWHsXocESnvVxrGGRcLxtViEzAxK4Fr8Q9"
				, "AWhvY9mQwsnhaPa9rFBud6aEUi149Q1bPT"
				, "AWi4pNVWMHk2Kxqg8wrAbvYTLBPUenxZhF"
				, "AWi9saRKofuKD1PpwL2vV3fmTK7ta8niLB"
				, "AWibiH9ZGZYEfpSY5auoys2UyZW3EDEL2w"
				, "AWiQKfj9jwWDj5wHahNz2hFT5jk6Movwin"
				, "AWJdNDpnpbitdfPVcCwx7ww9nAZyjGoeqF"
				, "AWjECs4FBPEm8GHFBFq1N8GTe14tGTwWq1"
				, "AWJKtNoDW7JHU9xEPBuL1VckbuVqV8PNFN"
				, "AWjrmRM7rC6YVKkP34yM1z11Mt4ce6WpeX"
				, "AWJts8NDjHdG2Mm2RZX3tv7kJmomwrgTDw"
				, "AWkcFBpFuT3zSnrFYg1waE1TUABHinNoTb"
				, "AWkd1LrJFK4CCT9XwSUjQqJLnRTQRonaub"
				, "AWkdhoMX439EihqZqagwcQdH5iwNtRiCNk"
				, "AWkE3FSddDsShsKFawQ9aqo2KWe4QC2uW3"
				, "AWkP9sKnt4qWWP2vCbZsHwJ51AqQudFeLz"
				, "AWkrLfpPg2oojZ3fEnhqZGQKtRxU6Ka6ie"
				, "AWLLPSW8jmqRLJ5NKsGRJeT3RKZ9mE6tAh"
				, "AWm7Uejq7iKej9KMhW6r7Vcx1n4CqEcKfG"
				, "AWM8BViaMFD39mBRgYQWHYvKNWfKPc7BdQ"
				, "AWMjAXGdG6znEcNA6Ksy6TrejCaD4s89jY"
				, "AWMksR6nHc7J4hQA68jVsRKg24fRiFLLBm"
				, "AWmnZCcKstGtdr7uksnKmsn79Trh2JQCw1"
				, "AWmRAKfrnfBi8vHNcfGofaccjhJt4PJ2n7"
				, "AWNQ7XMwLyHLvcYXfD6fE6ganddoXgbBTJ"
				, "AWnRfC41F6uzfGph8Ff1Vb6sJ2gtQYbKJL"
				, "AWNt8oV8aG1fb4dSj7ViHRuyCPJWLCfaVL"
				, "AWnTCHJhRJasp8sAiGqBuf7zW4rWgj7KFd"
				, "AWNTnD3WM4tdHpgchLDKEVR3Hr14hWhQKZ"
				, "AWnU2fpnHwL47h9BJFTSv9izxKMEyPHTEu"
				, "AWooLtMjGCTsyxcvmXkDwXrVB8eWwxg3D2"
				, "AWotjn4uUmqF41Bre3vhYS2kWwQ491rTZG"
				, "AWovtvWyxJN2YV55zrda6QzoaX8rqDDK2e"
				, "AWozyQ5ta2spfHqBJFChA4wSp9qeg6njxP"
				, "AWp88LEeTXAL4QUESWqVwWsihNT1zgYMzH"
				, "AWpJmehLD2CtHy4bba9aPAp95pVy9GTMQP"
				, "AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj"
				, "AWRJmToyYpGPs3igZvaCoSZW5zQxjQiCri"
				, "AWrpeNHiMmCGAJyL3KsZJ3o57zC9X8HRPc"
				, "AWs7Y9MRqeDA71yV25isqf7GqrwcZrG2EN"
				, "AWSGPvAfcXD3vZRb9m44gYjDzJWaCKDRbL"
				, "AWSpSLzVFkfd5XcXgj6vJfJCe3Sr6pqbeX"
				, "AWSrfm3H6Sv5fHSM91RBPNNZPaskkcTBBG"
				, "AWSuWwmoeEMJ1ApXj26yu6hhV1sUBtfDWY"
				, "AWsxXo9ci1cDtqwcxHL9YvVEQaNbb9DWEG"
				, "AWSYg8hKkegtuZq4KTfUDRKzEkaV8y91CD"
				, "AWT6FMNrRMkHDJGZcCxVKW4pzXGk26GwD8"
				, "AWT9usjcJxGmsqoxoK9tovtMGP3Hfn3pz6"
				, "AWTBrYQACrvS6CbwBdNbNKav14k551BhVd"
				, "AWtfnPjWbHvk9Q8gDR3dibLuQaC5CAufTu"
				, "AWTnM1j85jHuVcq69owh3zqzsrLkNmfGuE"
				, "AWtuSpcYBde1mL6jG5dVxGY3vDBugYmnN1"
				, "AWtwJuJHc94ERvEke7rSHhH6VPBKTwrR4a"
				, "AWTY5jx84AacQTckNXZ2CwSswYM5g8hiUK"
				, "AWu4RebZovCJyCdHeHEVyDEaW2hXBKvPF1"
				, "AWUgK8itXS7qtrvxgQRQV3iCpKTTEr1HZb"
				, "AWUK48k35UErWaC5QDRoFFzmRXKWhuwphd"
				, "AWURBDiVNhYmWDjxjRsvAZESd4xuge6nJ6"
				, "AWUYBV5rYRS6fcmuXtc5j6R4nR3fWRbtgs"
				, "AWv8efvuyPwR8oSAeLUbrgogp5GnxiodhT"
				, "AWv9cjsJb3YUPwNp256AKTEDWpKKUo3Wfw"
				, "AWVDPuXEKhmQLHk7Mzm8emmr2C4Q7RowRv"
				, "AWveFq3y3M23NdEPYP9SpjbZ3PDEpBYyS5"
				, "AWvkvRXiebGq9rCh5FahtxMQdwv2zC3JPw"
				, "AWvnhKTRfVU2gQ7iyE8h3RnPcb8q4B7A4u"
				, "AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus"
				, "AWW1d4nnYqZPYtBQQWdH4ArjvGwEwf4PHp"
				, "AWWbRqPvTmMoCjYLXLA2DJvbk8d3JkmyvE"
				, "AWWc5M9D7QMEmhEgYKuEx2Ab6kNqsv3sLs"
				, "AWWEgXqs22APrzQPEYV7LwQhLmbJ1gusqa"
				, "AWwJ9LAAruZFFbHGgSW2q9SeCcAkA9t6op"
				, "AWWrfiGSohNWM8BhZWKFguTZxbXi4H4H91"
				, "AWwtxQAVdVvf1aUVLkE1GFyFkSgVUdGaLK"
				, "AWXCK1TAC1jsZFGtKKz2CMq355QhoxYjF4"
				, "AWXM14Zyhpfp5VsB2VLm9u5qxfmDQpB63K"
				, "AWXMtgGpcsVKjJfxNg8fhUtUFJ9Cd7rHUR"
				, "AWxT9L81qPorvr1LjqasGhMp3oVvfVQJnq"
				, "AWxvbCGgditCgX3VxB58ukHrKnxRrxU7CB"
				, "AWy8ChJPkNTPxaReYVJn6Lhcgy7gAwXcEe"
				, "AWydT442yGMcVmwRuTj65FgcZHLBo7WxAv"
				, "AWyNtYJzshXGpNTyaDSjz5okRvt6aKR8iA"
				, "AWYrdxmV1qLm2mQCXKSXgiQkMoJmFWNYt6"
				, "AWytJ5Lzw9EPpachA5ErVbiNH1WRx45FMG"
				, "AWYZgtfAAf6TsUZxjook4SVeFfyDkqWASV"
				, "AWZ4482gdqqJwPmigaDyKomSYuDs37pe2r"
				, "AWZmCa2yKgwxh5Px9pZXDgaEpnvAZUfSFo"
				, "AWzNAiUMw2rx5L7q5JGffgrtEM1bUaAXb5"
				, "AWZNm9m5M9aCRMNCKXqAkNJaEXnLRPeaL5"
				, "AWzSikAV1QVYYPu2Y57hx8ogsGYDNzuw6r"
				, "AWzWLQMi1rJYUxYci7T1QLEbQVf48EbXhA"
				, "AX1TZ2JuZB1Mrjy5ki1TiB71zWPrntdyzo"
				, "AX1x7cA2wVwLNhkjBivAW2SjRHQ4GQ9Wap"
				, "AX2suTtMR5n1MxQk5DLmoNycLrCDWotKxJ"
				, "AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ"
				, "AX3ooDkp443UKJ8Q7sV8Yb75aKuR6r5WUg"
				, "AX3pi678L4dBnSGPf7BuUjvDhJyPsHrp5e"
				, "AX3uJFBHc5aEtgRLxQd5nr5e3YrAZB543y"
				, "AX45HwzbvYstsT4uwxQXVeCXVHqtPUrRHQ"
				, "AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8"
				, "AX4ym9jQJuXHK87oT3aHgYMEfYRkNigUfe"
				, "AX58Dp3xb1BV3P85p1TL3sqsFCNbHtDcoQ"
				, "AX5AhR7wT2dstqbhrg49tzv8ZA9JGP6neF"
				, "AX5jMh1ndQW9j7D3cyGyhEfvMufeqDFVQM"
				, "AX5KhxuXvHTL6b4Qj6MpouLRydqTFoee9y"
				, "AX5r5UCKab9ta4zTjtyC9Mby6h2tHuavWC"
				, "AX5riSMerewmX8YaLXi68932Wmdj3r92fi"
				, "AX5sPW3acZeKrRUpJ4bAFXbxL4jXVv5DLS"
				, "AX5TPpaphMP5HbGuFThu6QCSQFkiPjdkT3"
				, "AX5Y81LUz8ctH4G9THQt4dchQ4hjxw9mYb"
				, "AX5yU3nW9kmKJvRUnQQexgT5uaz9QiLbwa"
				, "AX6B3uKwQKXDYLkiWpponoc6v4Vo4fKCfR"
				, "AX6DSoH71qNEF2d2FqBQ2RB8VCxb5efRhe"
				, "AX6ohsQqVfbeBCbYAqq9snFJZCCxWRTr5x"
				, "AX6p6msZPJ1DsLrFMUdM4kMc7E1pR8BxgL"
				, "AX6TUytMHekz2EzusoHNfxNBGd8iMBWTpU"
				, "AX7aKa1CMB6wG2VJFiVoEhRHMCrbwGvcfQ"
				, "AX7Gdwpcz7CgQDqNvdLoWL32dcxLF6RXS1"
				, "AX7sj4MT6gENsTis4tHeZTGCrMn8FQqNKc"
				, "AX7ThoJtkqvL68KJD5DGeisW68pZ66pW4c"
				, "AX8ci9LiF3xnZ4GK6CAVZNFx1dkYGNgFgY"
				, "AX8EiAzu4pL8dkM186gnybT4PRT5GYcwTA"
				, "AX8GZ7YHiZ33TRzfpFgvt1ZKUkKaVHaA4T"
				, "AX8J6AjJWJuvhGmj7dXNFxSHY9AXkxjGi2"
				, "AX8qgYA48tLonaXbQCGEK1Q2JqmRRpmoEA"
				, "AX9ntwAJsKyGVyyCxAf1Kokkwvna1dQNgR"
				, "AX9rPK142J4YdreEbXWp939fCX3xxzSTK8"
				, "AXaAdUTVGkLk2tZYobKuj1ZtJpTZ7x5hLq"
				, "AXacuMc1aB7AJmphuNxxUZKZZQcuQMkJnk"
				, "AXAEfxF4EQGMUaQJXTGECL7gfTBdEJnMF6"
				, "AXAeP3z25U1hgWhbM25LPi2JkHhzgUB57e"
				, "AXaEW5V2rgwBGpFpEmNCt66znX3KPepRfq"
				, "AXatXrhVnHXtKsi5spbSmGdV1Te1eisVV2"
				, "AXB2o7efkb4bjCTCWZXN55rCr4rQdSsRSc"
				, "AXbfm2MkHJLvTiwkMbQMWTpmQMVqdDkBBk"
				, "AXbFTAcHZjLqNM1ZG6d6pNsqLwXNqEUHeF"
				, "AXbGamQ1zuZ3XZV1oSmFSeeoNJet3SQFvM"
				, "AXboZ2dXAsYtgFCCSHHsck9zVbf7YEireU"
				, "AXc1sPhi98w7VegaFmuii4pY2iMUUPjymM"
				, "AXc2txZS3BzvBKGsxoBxZxqHuE9fywa9fx"
				, "AXC4RHhQLWq6gzbfUPZ5EmTm29TACexBPG"
				, "AXcc85pkisr3wcmxycqRQw3oTpUDpH7CN4"
				, "AXcjdCGvt8ZUcswDhTu2ohhMA6Y8VCiM68"
				, "AXCu6n2LtS98kHzszmhWtF3v8TWYv7jHfU"
				, "AXcU9sLQMxoNaLYte8quBaCgzBsf17CKq2"
				, "AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J"
				, "AXd8Q43G22Zqqw7dWbe1XLNgUNpzxQCNcz"
				, "AXDB8pW8ifhyt8d24xxFixtrm3DBFDLAzX"
				, "AXDCzJdvwkMwa3TaQACLcgDjzhoZsMeJbV"
				, "AXdDUGRsaNEoD1MeKAwaUKTBxFr1NEgJzH"
				, "AXdJz3zadEf8xFq3GzHmkYvYkTRpcyYK2k"
				, "AXDuweinfXG57A6VT7ffpjd3STAw9q6FV3"
				, "AXdUxd3wC1J22WcJcJfkoiji8GnvAx53S7"
				, "AXdZojdvYYotv9UR4refZfoYBDcmu2BrT1"
				, "AXe3YGL6EwyuwwQ9Yg36bMWhigEUR7aA76"
				, "AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC"
				, "AXE5xkhCV58j3THmv85d2mRBnhft6muzeZ"
				, "AXEaGnDtrZMTisDbg4AABwjbJR92fQHtwT"
				, "AXEDfbAQ6pZp1NFByGTaub55D7FhLd3npt"
				, "AXEHWaa67ZLLpc4eKmPByqdJV71rk7WiQv"
				, "AXEkcdeW2Kn85YwTjHWwamNnUGhBvgHNAN"
				, "AXEPibQ9ZDCEmmM97DiTKtTLcpcuviStTr"
				, "AXEQcNXPGQ51zwDwZL6niZzrVc6vXSy2pc"
				, "AXeQdXeRLSkBkunyrBbjYVQLEA15GDSJvw"
				, "AXFBQX4FA4F8XmFpMf1gEWcueDkGFFwHVP"
				, "AXfegVaqqMh2QpvxjpMpwvbkojqd8apyXq"
				, "AXfi69nKQ8ZMyrmMJvXpd7bUpsdmnYXuy3"
				, "AXfN5iwLgHnbV126bvyjSomrVVLRp2t9SW"
				, "AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k"
				, "AXfs6JK1b7aZffZeqJHQck2H2JSZJDH5xE"
				, "AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv"
				, "AXGkzBZUshoPf5C9khEpNgeWSC35xwmgzQ"
				, "AXGr33xFtFSV4hh4tAmF5ED7ehF6ugbSsc"
				, "AXGRmtr35yuxdMMWPDP6ii7XDSKvpCbqGq"
				, "AXGWCmUHgLFWJmr3qYAyqbqaMLpRxpUFvf"
				, "AXGYj33q5CkHLxs4mtpUDWEQrixreugPMG"
				, "AXH49RpEmNT5Qrug8Kt4qDsyHvKp1r9F8Y"
				, "AXHJrpM3ZViaisv2izDpApjWRSajxhWg9n"
				, "AXHNSoCxb1AzNMCTKM7ZgMMoQVJRCA3WB1"
				, "AXhQvRLiG1z97ZoYsvMno9LrDNTek6xSTE"
				, "AXHsj59mkLv4pwu8ULmzTL87oi1bxbdStF"
				, "AXht4JWU6SF3fJaFvrEPPPqjHUykBV34BQ"
				, "AXHYuDJ6TYapVPARCfbvWo43RHyXqqtmor"
				, "AXi3zZKNwGcjNuDL5bXx9aDujyue99Lv4d"
				, "AXj18NuibtkHSJRYFiK34veviNRjwu1EuQ"
				, "AXjbBixW3BKnuXndDCV7JdbBiViFJc6nGe"
				, "AXjcMgab6rRkZHwj5YQzyqcFhxQk5aVbBY"
				, "AXjhAsMVc2u6RGLWi9AVgPyMSthL93PXYQ"
				, "AXjNcSdw3YF4ykLccMGVkGgJguZjmhSmTY"
				, "AXjPjN3epBnETbQen6zvi5RkxkjNsVqhDX"
				, "AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN"
				, "AXJWnt6XQxxU6N7oyrCDhwCxFWtdJZJ8EL"
				, "AXjYKWMtcGa4xSVBmPmhyzxjMk7zChtCs5"
				, "AXk1QnoKjjfqPkcWm4aoWGRfrAr7ceeuPE"
				, "AXk3aWPMsosJR2Wk9FDEmWiMe7zBia6THC"
				, "AXK43kZzGA4dBeWqbW9ioiMYPwGYnMwWPX"
				, "AXK5TsUtvG1UfkQLmgEczG6Hjnbpiw1iiq"
				, "AXKDgWkpQYqriLk4XxHwwFfmY73JVePMcr"
				, "AXkF1MserBxd1vWYPsSHffuz46x8kcHgp8"
				, "AXKfFaoPq45unhLGjsfWwMcLRS7tpPQdow"
				, "AXkFtZqVKnNiLmyeM82Webg6WU3atUJ8N6"
				, "AXLcwh1ZrX2anfEVk3FoR7LotiKyXG7wVE"
				, "AXLt1FVtTvbSiKmc31MMveiabrRC5ju7bS"
				, "AXLuXQaRKQfxejBNjCVmR9EWaWhMfZv5oz"
				, "AXM1w6MrBDVq4Q62iSFu1TKot4jdwgM9XX"
				, "AXMCUMNKD3rjtmjAQM7Rnh6pVuSkEA6EqZ"
				, "AXMENSPU356s5GsQUpbwcxXjcidC5EfjA2"
				, "AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh"
				, "AXmpWmcWCAUVTXnbRrbi6exNQM2zpQFr24"
				, "AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8"
				, "AXmxfXCELMyDuprQQ6rmPaW17VL5wztfMD"
				, "AXNdW5XEVHp2ubshda1ZsEKCwCzHt6ftiw"
				, "AXng4Jh2yyn5vxxxRDWgRmXTFkA9X678hS"
				, "AXnKBvHNA87mTmhjVgMwhhapo5ULuKun16"
				, "AXnKo8YdNzinAL5MXKbTt9ZPygFeviAnVy"
				, "AXNMS4Apj8MQX1qwhBzumsEjsj5Dse9Mhr"
				, "AXNoY3BJzS6vJ9PKHJPCCpsF2jkTxeC2GH"
				, "AXnTSghaM7HGpfw8od6rS9bSNhjTKT2rhP"
				, "AXNxKsi2KjFTV38o1wX4Fwj79r136ZfE62"
				, "AXoDi2fPaqcX8z2oRe4sQdVv9bpmjMCi6p"
				, "AXoTMeSsPC1nPgLG66RFwvV6D1wMMReeQv"
				, "AXoURvK7YSfiuG7XAcSa3vsF5mwBYKENSX"
				, "AXoXqBPty5m6vT4LjzetH3AEQ7RwKUYtKb"
				, "AXoxXSbTgESYGPgJxKTbYSirHqRjR7Ro8H"
				, "AXp5QcK17Bu4PE9dRbqgjNFesQAYmCLeCf"
				, "AXpfkJv9W9qvbPBuTLsLUtuDmNFAC5CUEV"
				, "AXpVkwQADEUgwwtj8kp5HXBr7hZgPe1VYG"
				, "AXqFHbAzVkCLcxaPXkr69qoxUq9Vc8Eu89"
				, "AXQHdBiS4E9cZtCcsBuuu5K9bhEK12aW5U"
				, "AXQQxmAD1W61b1o6bgCidLZgNpW1JC714B"
				, "AXqrUnmr3FojmxFDPG67MhafRrr7Pr9CmP"
				, "AXQw75S9Zy2UgqX5wV9ccZnC2x4KP4TC8m"
				, "AXQx57ZoMxHsmVEEHLA52RgLjcxjPZQ4mZ"
				, "AXQYzd2aoeie4Yf3eoFgBgHKgKon6tbcgZ"
				, "AXr8H53JetbUPxKYcNfYgNtct2ZJRGdCn3"
				, "AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY"
				, "AXRtLPhpBgu4oF5tnXpGePKftaNFSEVmEN"
				, "AXrZzmE7bk8NfxFd7jnh65JvBNV6SfzHo2"
				, "AXS3hRD1pX2tbPbQKgukzhyJbb5cMHP9ZY"
				, "AXSGrNL8GzEsGHc9retZcHPJfi2QfrGeRS"
				, "AXsjw7RCGhpE51ChDs8gurqHL8Fiaa3tQG"
				, "AXSkMR8c9ocnGcHH3boaEjy9N8GrWXrhKg"
				, "AXSSz8ae9pQiN6K2YxNJa9CA5pTkEEJnSA"
				, "AXsurPoXjhWGiqkjemQyP4DRjNZA8SL8ku"
				, "AXSVkJhPVNZTdt2VZzg9Xdqa9GNEfN6zTE"
				, "AXSXkZuusFkbL9pzvU1HWNtxUJreaTdv5t"
				, "AXsYznTLRMjVyLwMWFkBWkF1se1xqB16C4"
				, "AXTmnV8xDQLB5FHCNLuRdmddsmBZLnqQmJ"
				, "AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv"
				, "AXUhWvurLwAxNA4tK8kC2cTxB1xz5w5CNt"
				, "AXUKPFDsV4xNhDw6Q8Ywo7zbEaiHan1bUL"
				, "AXUQUcRHhZD7LJBHpSSFp6uDAzaAReib1Y"
				, "AXUrRStMDfSkCZ8h6hBjVNeJvZSDPChtgP"
				, "AXuScmZG7kzJr1b13Xa99ZthqjFN1NsAXy"
				, "AXUuxBxoM97XgiXZc1VyGj1UyPBYcbwALs"
				, "AXuWRzVUEgSH1qZUTQaP1zJcgK4BQpSPB4"
				, "AXuXzj6RtJVRdmRgEjaLHvyKg94yh7vScM"
				, "AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH"
				, "AXvBurfXECnfg4nb15CcgHyp9o29X2rs73"
				, "AXVDLmQfHb6iTykkHXF8caeSjCbZhEWs3m"
				, "AXvfk5ymMfDy6n8iz1949Naxjh4sq1YoRA"
				, "AXVkkg5NGmww9XabwDKGELjqNQm86iQTTj"
				, "AXVT3RKCzaY8k8sCzJ5H1F6dw8Er2HAJWL"
				, "AXW64tuxybvmvCDTY9EtYzdwjzHjJfUgd5"
				, "AXw6nGUD1dvgjUnmHvdsaWh7Vi811gYPJf"
				, "AXw8uDxNvgHhLREzLrLQ53rqfAanbEGexh"
				, "AXwd6t4NHkJeLBUWdjzS13nYDPGXXmJLyX"
				, "AXwEiJjCevjswTy19DhATLsLyLQUyR4kkZ"
				, "AXWLizpFomt7YRQ4rj95WVFwk3wkrrUDpB"
				, "AXX3q2jy74iu5odi5rPfz5g81fbvE1gWCd"
				, "AXxe4RWkHwTzZi37PtQVMZcgQHMZXEAHzX"
				, "AXXKNQ6zYopYKmyAm6DkBwQjLeyrgCdQh9"
				, "AXXVjBHfy1ncZji83L5jPQGQQi9ArFpXXf"
				, "AXXYbQUQmXHJCJbeeVSzuMpKv2mBNQpsmL"
				, "AXY2BUDLvnLYeKqSo1uugquGNaU7HGuVcE"
				, "AXyfsqtDMhznPjuAfzWEqxYUmNdM8XGKro"
				, "AXYo4xYS2weQXZ82W2pawmukDAcBkD3k2v"
				, "AXYoU1fswzJxt7SPkaE5f59mdtmwA1nAsU"
				, "AXyQw5tfV5E22LpAcEomWzdrTHMsd7U6aY"
				, "AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE"
				, "AXz5nKWmRWZBs4i7nKqY4LKh1z6iCop1kM"
				, "AXZ8MXP2LyE7aLobb7x3fbjSh6a3YzsENg"
				, "AXZex7EWuZhuZJQAVrHvieyRsoVGi1GSTo"
				, "AXzhAwCJ7u4Pf5TVGU3CcN8EbMAHE4fvmv"
				, "AXZJrdq5wycUfTWooZn5iUTkL7HzVW7pnE"
				, "AXZoR3dgJy1NUXCsxyHvpG63AWtt35ZHYC"
				, "AXZY47Dr7HGzHqZP3Bxn57ctPqVKEeSjeU"
				, "AY1LMMXA1vrJSKBWeW1D5Xm5XcMPwVtTFL"
				, "AY1Ttha2rnSHjDpgDMft29vmNaVx44iL4T"
				, "AY1vRjtjCsSEUoPoxkXYgjhA9JMP61fY21"
				, "AY2BXjz3oAcy6WN6T6e28izPZGWhoAUj7L"
				, "AY2omvXLjt4ahL9EXF3W6qynSF8ybTyuCw"
				, "AY2Qz31UKDWBN62dBZGTBKpYGNXBw1FivT"
				, "AY392EPz8BPASvBhuDP6tqDcmjpqNRMehr"
				, "AY3ARuELWsEpgza8KWtYhDjJ7U9LV9t9f5"
				, "AY3kesYxXnctekKf3BQnmoam7S5LC5J6aY"
				, "AY3PasbGW3REQjKBBnVT1H6Upf58wTfoWz"
				, "AY48jhdVFZDMn8TmrQ4JTC1ZSS14UJgHFk"
				, "AY4fZ3L8oaSYwZ7pMz3Lwibhp14zvAcJC8"
				, "AY4MJZS4X1c9yUN26w6pYWdkdSueptdSqM"
				, "AY4v7JVuCCq3uHmycccz2LQe97pLmd1hyM"
				, "AY5iymu2M9XVNsrXAtqJwtKagmRPT6mhTi"
				, "AY5JUr3Ah2pVxtUyc32T8GqtAVKLNM1BsC"
				, "AY62AqxRAKXpWuuPEZo9AmxspdAVvJAx6d"
				, "AY6qBZrBQg6M1xvnYRmafGY6CyXKKHWuLH"
				, "AY6Sby3o358ZUwhUWhSoSHbttT2H98j1oJ"
				, "AY6x7dLnUajj7u7VT73f7j71g1UbU3Bu1r"
				, "AY6X7pAfHHnf3e5N1aNRtsvaciJXNvxWzQ"
				, "AY7DSdJrNtp9VqU3vLd4EaqRVq6ms8aHKs"
				, "AY8AJvJL41PxR1RSsEiE3ZEtwqrtxt1bde"
				, "AY8MK8DaCH3WyZnwukJNS6k8RnkNuVvzUT"
				, "AY8RaxwaPhj9oEVRpVGWAuBiYTxyEX6jcz"
				, "AY93KPFKH9pWLJNH7G4fRgC79fvVobDg8Z"
				, "AY95A433M9ewZ3YVbFxCeJFwiz8WALuDg6"
				, "AY9EJqVygib6gPweo2mSspTcQXkFQ71QSp"
				, "AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ"
				, "AYA4ZESw5ed7JBnX99aRNC1ubXCpSrQkfp"
				, "AYABt79gxr3WPgFrwnEkSkCYYmPCxoahq4"
				, "AYaCkBQeU2Z2KhDZxKWfmS1u4L4PtU45H3"
				, "AYaCVDGKZLkpdWzc78KzSx55BXWvNNym8n"
				, "AYAjExJwyt83RnUG1b8AyTBFFtaWGxtgLn"
				, "AYAMhtK2MLsuJ5nUSNfVzSJtJmv272WZeb"
				, "AYaxgX2wWaiEd3v4G2x5cfqh17aKoaqhBa"
				, "AYb59bpbSsSEbAt2g9W6BeAzvhndvF9f8m"
				, "AYBDFZCMkmiPN3bdWpg6GbsMjNUt3Y5bgT"
				, "AYBEucmAjWgwySNNhKtzfWUbhBDi1v79Au"
				, "AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN"
				, "AYbnpXb9hifr2S4RozECF4vVC3CFKyLk2v"
				, "AYBS1zgrx7V11AKyjU4RgbYVmLEAYK1h4h"
				, "AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK"
				, "AYCjRRi2LLm493JcvFryw4qTcG9MBgdHac"
				, "AYcjvjUikQ3QNRAjpct5LB2rGNbmeehbB2"
				, "AYCwXnpYdwbYnbwX7qnjkxfD5dLLWZex2C"
				, "AYd3ZcTQ2bSbuLfLYJKuRKJ1QuFNAAvNGD"
				, "AYd5vhftZQUdfdZQRmFtc2ZvBrFrEwbzbJ"
				, "AYD9BrsZyRBqxZDjmuqqZbxdP5JDXJUJXR"
				, "AYDkcqaDRVa6bwgJQpJnkm4eM7hNWZBEaH"
				, "AYDL86Rp4is42bjhGRFtuhv9x7wLVvZrr6"
				, "AYdPGorvbaXh9CiYuzptULi9UKYyRdPsHh"
				, "AYdrzSxM5N8YKbeabR8dM5ggDm97vWFj2f"
				, "AYDvDbUmGnqpE98ALvQ3ZKWDaM4WHaT7Zm"
				, "AYE5sZ5xzNv2B3w8jZ281H1becpjTUU71v"
				, "AYe6dz8Eo7RLLHCu8ZyBZMx99mV4qE49PX"
				, "AYeEv8wG81T1yvtQhk99xg6DSrp9F6ymET"
				, "AYEGDR6wyykQ4suteYM98VgMGHbJBZRciP"
				, "AYEH753qwVUQJwiwAot5NPby3aJyevCLek"
				, "AYetvNebLyv71k3NjCvS1qUkPSfyB3XgDV"
				, "AYF5mEkcL8V9rxCoq8npWdBW5nxAfeSyqG"
				, "AYF8MyfZPnQncXD5XGmGaXM41RzX9Gx9ee"
				, "AYfBJE6NAUjdkhjHStguWCPqbTj5Xa8RD4"
				, "AYfidVEBT6oycBPN8oWTe7JmjVKmANrRL2"
				, "AYFjwB68LNji51sP4J3pHWJy4YfxLWypKk"
				, "AYfU2nokmEAPpMKXss7unGRjUVvuGEMFSb"
				, "AYg1nRni13rfNcaaHgQBovgr9VinjKgeKs"
				, "AYGArCK3kdwittku6vuP4WNcH3TryzdbJw"
				, "AYgEH26R1TZz1aqPhdZSoh7eyphyksaf3W"
				, "AYgNLpCorJYTvyU7WhN8c9QT9bRfVb1xZr"
				, "AYGtC6TwUgfpaH7QDLwKVA8esiQDa4pE1e"
				, "AYGwTtjDDb5DTSxNLnvoNQobatNMhiPM9U"
				, "AYGX6RJRC8gFz7hRZseKarGksHCZoSAF7E"
				, "AYh9MLm9GajVL3EakQdyNmchA1DsXkrRbM"
				, "AYhHX4KD8NPdjC1v9DzY3WVf814LZRkeYo"
				, "AYhmWAfGiJxpGN3CJFJTVsiCh3aLUPGrpc"
				, "AYhQCTQLbLsA2Nro28GAcFWgfF61DW7Hn1"
				, "AYhtjF3o3j6yBMXBMenBAXaiY3hG5GtvY6"
				, "AYHv666oPUyVC7RjWHS6UR5TWUHYeU47Su"
				, "AYHyywqMtdKK5yrfVJ8SCvPmeXS3sAkMVA"
				, "AYiBq5PMsNPkShrKGZgYpy7qvuZq9NFDrz"
				, "AYiJcvFokaQjcaHuYsjJqxfGb8HM5nYNbk"
				, "AYiQu8emd7q4wHWhitgaH6BU8xTxbSz3r5"
				, "AYiTxUdSboYm7MHgCiDxGhQYdKEWL7szUh"
				, "AYJ7MRrfjLbzoYY5uRsMSSEWVBwxfoNEaU"
				, "AYjbGmVWj8ApxuRrE9cF3R3K9R2DggadFR"
				, "AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1"
				, "AYJioeGKyqomuoY1UiSwgiNndZZjkai2bN"
				, "AYJkGMCF3cUNykKLYBkqxstaNAUaxhwsYt"
				, "AYJoPi6uDvAaTWks41SDYJLM6LrFpDu1ZX"
				, "AYjx9jZyFbRFjgAiFsodFu8E2DJK73QN5a"
				, "AYjZkpotdjtX5EYxMq2XjTzbSYBpxNTY92"
				, "AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7"
				, "AYkQEPM5Qz4C5RjxX23Z9VNiwXPvN4DNRJ"
				, "AYkT248hhhbFwDRjwPavryXjaGVKknpzBW"
				, "AYkTJfhRk8dGV3HEFN2rP5RUXQuJ8bSnsW"
				, "AYKxArkpjxdk8kbdmgYV12Jh3ihzjyr2iV"
				, "AYL3Kha7QYY37ckpuSP8oDKFNbWrLoWfQV"
				, "AYM2qVsnN2ma9gVonfPGFJmM8re5H4TbM2"
				, "AYM7F5S3qkgohLvw8J2bn5vvtjc7Aj13KQ"
				, "AYMhqQQk4edMfjjpF8wMpAXUw3GeFqMEn7"
				, "AYMHx976Ay4JZNjpTLwx241v6PLzHiA671"
				, "AYMJKPwkMR4bjF4oing7xuwtMXtD8cHNcG"
				, "AYMqfjMYRUfCGaaBX1SFA8XemVTceXZCdf"
				, "AYmWQYj3iJmM23tcjRpvmvnshfdpfKEnQc"
				, "AYMXdwD4tFxQnazvPPRjLKamAfYUGny8yi"
				, "AYmy5h8CFDQefdVjR7WZ3nNaxjVMqs4dDL"
				, "AYN84Fvb65auSCxyp9b8rwsJPWkRnRW8A8"
				, "AYNaupMtBmeroy5nz7cmgsL7b1zEQumBmN"
				, "AYnkTTap9iW91zEZkCbBwYr5ePkMmR1RbF"
				, "AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8"
				, "AYnq1hGFXnpyDgN7pHbTZc5EareqgAAqNZ"
				, "AYnRsF3HbVdMmTAwcyuzdf48fg5iGtTUxh"
				, "AYo8Zdyn9mt3CxLZn5pEVvY9HiVmnmjGLH"
				, "AYoaJBriDihzSzahXQiQTLciW1h1kyHUcC"
				, "AYoehmhVdxikcu2CcVSzXDAFB5zexP3VJj"
				, "AYofgcLep6AYdDXgxG7uDXLi9bB5nnWbVq"
				, "AYoVZxZbTHPPApSMH46aNZADkQ9KFdDcz6"
				, "AYP6WXPyFTsqCvjTJTe8yNYcWxwBu51t3q"
				, "AYp9RWiAGDE5gFEa65Wh2yERE4pismLRPc"
				, "AYpcjm21LEbhoGqzmsExawqirQV4xMDgdf"
				, "AYPFmE7CzvuW7iaPCosU2utEKPojgaAedZ"
				, "AYpn68Ju55RWM3FTSfxsaPRUBxebDvQmYt"
				, "AYPqhkdwaqSuaE6gAJZbRQrJ9ps3PRCW9U"
				, "AYqBNg9DNMd1hMpzGHAgM9XN2k673dCB24"
				, "AYQjanyBqNx7EckJXH6Rxi2qASzKg6NRcc"
				, "AYqR5uT17a6uXQETmczPJmH5A1VMRxBiYv"
				, "AYrBFTiifEXkuvpGaoMGf5mxthDg5vWGCj"
				, "AYRDpofg5fjUkMhG8p9PevMELeRjru2hoV"
				, "AYrwHyVpbJppL271dR2onLGm8GzcCQKpbZ"
				, "AYS6RK9xdX866DAJdyBdxWuoDxwJBaUsxS"
				, "AYsrFWy9Q45tRkRnbYSAMy2FeLJTuNYJ2E"
				, "AYSrM87vAc32UKWWPyt4UA6k41Z9u7bVoJ"
				, "AYsrPspDqpAb7G4urbt5TgADbr5Tun7goh"
				, "AYsshbTa7RLMHfUsNh7vaULWdDvhVDLWTP"
				, "AYsunvoRn55yhEQ9sZE3uBr4pYaKgjeavU"
				, "AYszSGjvxeiVUuGw6KsKMV6ghiJqPMX1mo"
				, "AYtdhzEDnhVvX9wMVXrCM8HPgoUFRiGEfk"
				, "AYtV3JUGwQP3VTmua26QHhmYCcfqrG5g6a"
				, "AYTxmUXo9kD9J1RuHw3vqQPfNkfi7sjrFv"
				, "AYTXozuNAeL5fRaujK1b6cnacNuauW3aMp"
				, "AYU12SxANoc7vP4fSzm5ZfpfVMmH6i3Efn"
				, "AYUCRefK311nK8XNYYdcdR7SwVCC8KrZn9"
				, "AYURHqA5e8M6Wx1apgf1wkPNQRFiZG3dXy"
				, "AYUrPj6viJCeziExpMFbg2zX9GUw619WTB"
				, "AYUsKdRXhJcuwBHjuznSXy5LrcJymMXGN8"
				, "AYuSuTpU9stzPmAU4w8w1af7LDq5CVipVx"
				, "AYuxFE3t4N6AoCEgc9xh8hBoMWhWo946vq"
				, "AYUXfwZHhXeQRfQjswN9pZ2JWDv6QxTSbW"
				, "AYV1U6148Qf1kotmr5A3LYpHuNs7UbfiTC"
				, "AYv7NzF9iyGz3756KfGUknEthjF2tkNcjr"
				, "AYVLsGaE5iSimJma3iDY2EaDeTw9EhbqXb"
				, "AYvNxsSazG9A8KnZHRe1dA2C96yWHv3Wmx"
				, "AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH"
				, "AYVVZYzoPJvALum2iSDDTKx3uUdhQdiEQe"
				, "AYw7ziYXFfV2UNFv1CrmLqSkzs5GMEd4HA"
				, "AYwxH6JuokSgg3XWSnaKVJxYRdMw3Q4GcC"
				, "AYX7TaPhUqZmQHxy8aQ6gj2synXHunHw1f"
				, "AYxkgJwkJVMn2bSq1CaqpLbc8gmeynrHfF"
				, "AYxmNuGZwxerso75qwHB1HTUVe3JQ1u36f"
				, "AYXRUVvDcMcNp6Q6Xi3uRiVE1P4jqFAMGb"
				, "AYXvhVS7kPv9yVfxaBHttqCKznf5Z69Za6"
				, "AYY2Wozd8RbFdepBVN2RwZB9a6qA8Ws4VQ"
				, "AYY6W8soVAHNeGoWnSDKC27PA9svX1F4LM"
				, "AYyHqJieJp4Gdhm9RwMYBgM3JN4VDEw7LP"
				, "AYZB12PVxkbnD9K4xV5E68SQD5VTvsAcU5"
				, "AYZefN6AZfDQZHQmYd5kS5w831iVrzRq94"
				, "AYzLcbAemSF5mU5decLgBDjfQur8FW3FTT"
				, "AYzmoZfyGZwddyiB3JmEwExxT71yBkiFpH"
				, "AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi"
				, "AYZpshAPdZxxc5QUeZdiv6MGt4syvP6f6y"
				, "AYzZ3MuMUqXLhjjvFjy2CG37p6yCAkYgfo"
				, "AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE"
				, "AZ1B2d8iM99ho5CtdoD7ypXpYbuvKmRRGB"
				, "AZ1Fmnx8zxMj67MXPa5AqGwprMiY95sj4V"
				, "AZ1JmsiCJ8SwTEnEgTH2Pqwf1HhD1Cj2j3"
				, "AZ1vkwBu9X8KR9pby8yGe8ghBLa1tY4PW6"
				, "AZ2GvzzTCuGMeZwW5AMD2xB8E4b3WXiYk4"
				, "AZ2iPz1ajiVpb8Sf61SqKnHqXqSoTqzpoK"
				, "AZ2py2Poiv4dAnhAEQ3Ubgi9v6YnUcURjc"
				, "AZ2TpNNf7cKdHJgTeYeYzhZ63RsoxTbnAq"
				, "AZ3xFtvbfL2K9LeGBsLtdr7y25DveoN9JR"
				, "AZ4h1KshaxaDrbRAdFi7RyjVkz4Epyx1Ev"
				, "AZ4JjNbehGDLGWN4QGaxSF1tdUSySQzv82"
				, "AZ4kTi7YZX7CjWPY34465gseWiugA3fz3i"
				, "AZ4KyHKeEXvPe5BeQ9yfUgNZYN8yifwERx"
				, "AZ4uAULmARpZoGBfswe8DqayE7xrRTttoM"
				, "AZ5EgQ2GnhjLmVsZaz9MyDqK1rzU2irL5G"
				, "AZ5jEKpnVH6dtcUyCGBLhHd45sHaJ3DcDX"
				, "AZ5URAgRHtMhhsDX2fF5yZ7zXKGP8sbySq"
				, "AZ6dND9grQBgBosXxkUGgQuvdDn7C4Bjct"
				, "AZ6oC7K6AvYbUdqGUg4B7tmD2wcKM8z8Cn"
				, "AZ7iBTBMMKKi2LMtbHRDayRodUnSRYBEBc"
				, "AZ7xeUujLwFjGBykfGsHfpgW8ZzuWaMiVp"
				, "AZ81GwHuKoHphtK56YTv5z37arSmXX2kSq"
				, "AZ88nwpH8aCSk81QUQQht3VzBTg7Z6UM2T"
				, "AZ8pfpYpG8NutB5v8jg2g592sKDBrjQzdX"
				, "AZ8PJNBB3fDnrvkJGPcPs7PutXztca8Ukx"
				, "AZ9aHBMPHPKp7jiucsWUFwT2vf1Qer7ew3"
				, "AZ9J7HSzJuZcK7Na79rYowMHxYoAW3nXdk"
				, "AZ9PRnv1doCrqBAhFvAFKcjFirSz7eDKsp"
				, "AZ9ySv9hm1SnQPAnYQLEmKSiv618vCAQD5"
				, "AZAfUGS5W5jCtVLajikGQdXQbxQFQruSBB"
				, "AZaGtt3oEiCACT1QHea9sjmTtFHSoJkuFU"
				, "AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3"
				, "AZazQBateDC5e5TNtWFLqkSjkj7X2vc95G"
				, "AZB1PiC6S3uJoFtf3HsbRj3XsMRWfqLG5h"
				, "AZb3jcJ5bWQznoG6FouhbfeH971NEzTHai"
				, "AZB61wiaQbke2t8sVFovLYWJLS4UNu2CAz"
				, "AZbaiuxtFZtmmFJViuCuf4EmNMpviZ8tZq"
				, "AZBcKJ147unzggdM3xM7QHYnMsDnai3wbX"
				, "AZBLNdxsPSyK2qtAD4BJYYugwR7D4dVRQN"
				, "AZBTYWNAViLQpWSU4DcuDc8Rrb1663BNJu"
				, "AZC6kkeQsMwgKCyyb3wK1HdbnEeZDvhtJn"
				, "AZcbBkNVR2R8rVD1pARVP2pDrhsunoyRUp"
				, "AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm"
				, "AZCGwLvLqwzgrtNNqufDXTz7WnWkKJzZJf"
				, "AZCW5BoB8bpiKpCWEQXbUCLe5aEZcHcEYD"
				, "AZd87Qp3LsGWEY31VJAzfneNM5jh7XGPSG"
				, "AZDAHHEB4t3SoBnTRVPs8nDdpmvTXxuabC"
				, "AZDCcsD8n3gm6UXCAsGfjGTJ3TZe6Pod1H"
				, "AZDdSv8jcMBtukec7MCSqkX1qKSY7rfL1e"
				, "AZDn4BBoihfRTPWA7hKAFhmQP3wbZ9asHB"
				, "AZDSYqn2JBmpeuWscmFwScNTcjLFxwApEk"
				, "AZDXkB9UrBzfvAhJVapN3LVmYmZQf6Lf3t"
				, "AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL"
				, "AZEBEW8wuctmkCXrm8sDs3szBDi1SCNBjY"
				, "AZeeune4Rx4QSRbiff2wcxBib2JQQFSfRo"
				, "AZeiCVe4QyWQqoeFL86DJyfStB1oana9jA"
				, "AZEJUcjKn9rhvJefh23nu8mCJUyVenueQy"
				, "AZEKioJ7MTUgzs4TAbx2xWanyVLKa6e97m"
				, "AZENfhQqNY8oxiWQHwgfjfGt6Dj2d14852"
				, "AZeP7JY8aXWF9UW4ZSSKef5ELjnqVFrHuE"
				, "AZErBSn795Jth9kqDuwYfGmLAFRTMAoJks"
				, "AZeRyUdHxMkSEwfp86WieJUvuohXWcPHGb"
				, "AZEsVPTkE6TeMCkBx1rgbLfC1jZ5vkzKRn"
				, "AZFAmw2j1PYM6WvFgK5teQpgUsxhWN3uFc"
				, "AZFBvCpnk3Um4nECMDVS4g7TRd7nMpQVAc"
				, "AZfBYyBpcE1tS2kve8o5Jav7pinTmoaEUY"
				, "AZffkWfn8eGVKm1ZFwjQLzGtGT8cwC9nwC"
				, "AZFGAwXyMGsK3eojaxAPjQhhhVfEdCeTcq"
				, "AZFmgLFNmXxBm1ihAZv6Q7Qkt6hjJXPEez"
				, "AZfru1uSwuMPN9XbaPCvqJkQExmTHRCTfq"
				, "AZfVBgcyKnkuayjjaQ2ezj7yUgMz3G8gph"
				, "AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP"
				, "AZgfaZe6yqxjahn1JN94dwgY4qZ8FAexVb"
				, "AZGvT66NcExhDKCVAx8jdkKQiATPprwvoP"
				, "AZhmM13BoZh4VQsNxs4Mj7g55YoQFRMKLi"
				, "AZHoEDtbsiVwptiTcehUfSo8L5NUUcsFLr"
				, "AZhofFgChXWwCuBrcZhpK7Zvywaz97iQ9g"
				, "AZi15KeYYiW3ohMEvzk11YHFD6Qr6GY3Ao"
				, "AZiSQxYAt9iHqs1qLirRnKrocHWcxJbJnJ"
				, "AZJ2mRxeHxau6RjPLmc3mDmY6PsPKQKFkd"
				, "AZJvnUpASXCZsuQMFmAUVS3Akb9DCHePEc"
				, "AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx"
				, "AZK5os2FcKiJiiQGG2ss2i37VmgTaazrdL"
				, "AZkcxmpyQtZBhhWBcbUmsPdPTYxoy6WVkQ"
				, "AZkdqB2ZyLEyEFH8Rtzncj5QhJ1U2YhCZH"
				, "AZkjANwk52hyN69AJ1omwFt8JsJcjm6Zon"
				, "AZkQY57qfqurhXZAyHw4wFA55GxKbVKUiX"
				, "AZKSdQGeeJkjfCvkrwvGH3oz4EK4iCapQg"
				, "AZktshVABoCyNwRak1a2kntMtTK9jBGon4"
				, "AZkw54RGGUMxJE7DwvEXitH6ZoPojBUKnd"
				, "AZkWJBCsrzBXHNxnPWM4x3tuWdTvjCvG2R"
				, "AZLaR6x4HW1ZT2CM7LSiQjZEa3AzJsCuvn"
				, "AZLg9n3B4fWkEy6wMkWk3cJ8nN8VTBo4vG"
				, "AZLpvGMeEyBu4J4Pbh9BKq3gumxNz65225"
				, "AZLRdqFzzcRa5L5TKDkNJT6r3SDogLLnEL"
				, "AZLtsHgWDFKT4ff3SQS4NPAQqejFjw5rtQ"
				, "AZm3irsPqpcxY7M6kmAf7V2ssZr4QS5eUL"
				, "AZMRwMPJXPSG6d7eQi8XJrjjj8PRMVGZhm"
				, "AZMsbJGHBoxkSskM9cTXDLAgabFEMX1RAT"
				, "AZmWTmyno72K7CMgBYnX4PtQisG15daNfN"
				, "AZNF3WU8AkGj38JXjd4rhpYXTRQ7HZM4ap"
				, "AZnN7iftyaRUn2LNyeG6eUvpTCFokpZRL2"
				, "AZnnKijmhUmZvLuJTLuCfbrWvJT6QwKqXH"
				, "AZnVcL8KjBvLg1fD3UeDz4di57MDnqqQJ9"
				, "AZnzLBgbMnoijcGxA6HQkWhQ5ZFgHZ61cM"
				, "AZoCnsuobJzU1QzWdDt2ACdkjinkz72uvf"
				, "AZogzkFUCfq5ManA1pzxwn2YdQnDedL2yj"
				, "AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4"
				, "AZpbCRFbjSZVntSgKZSJggQiT41sRtvtfc"
				, "AZpjLjdBVg76SRLCuCGooZ6PhfV7HQvDW3"
				, "AZpmSzaLw9EXV4BwPmH6mFkrfv8gPnjPv4"
				, "AZPPDHsfNs3M3a4w6rpuapP8N6cGoCp2rh"
				, "AZQ2kAPT8HzC9B7uHfBS4A2dT7L7f8nRiU"
				, "AZQay9cR9m21Mpv8QuQQkiPtg1byFgTbSy"
				, "AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo"
				, "AZqK6P4uBkUh6WEn9fshdaoZoLHmp9c1at"
				, "AZqsQ4yVcg2PxNKc68NSwUg2cPpW9HHgpR"
				, "AZR5wE452yTkkb8J4RUWXUHMkhgPCxsjVx"
				, "AZrCwJJkskAZtihegoTA17cgXW2VmwBNXw"
				, "AZrfRsScwZqJa715RCofLZyYhfSw9jYMPF"
				, "AZriC13soRMHozJksVz5kSGssVmX4v4CbZ"
				, "AZs4XMZiP1g8CThzArKto5NtTPU5fAXPWN"
				, "AZs6aZq8WEURbb8dAPdLC9THcvyyKRDDU6"
				, "AZsE7Eih7T5mwPJ5eAAJKh8PV4xTUsyxFt"
				, "AZsuHL27rh4HCQYABgoB82iB1EJjFVo6ie"
				, "AZSxNgY87CjkMadbW56z6nZGxf5Sd6w6rn"
				, "AZTFXmmDcqZjj3WNy2AgqSehHm4S9R2qFN"
				, "AZTHY1dPR63mmUvqF7LG2hgX2oSgRkSgL3"
				, "AZTiTddxe3u3vuwW9a9VZznJQAgiK7KqCC"
				, "AZtomvjQK9VgmMRcnSnbDYntCgMiGP6Q9x"
				, "AZtRSfF5KRgBLArajca3AfrLUYBFwy233u"
				, "AZTUQncAppSYi76g1UunnWyKjdXcjsCT5T"
				, "AZtXqKsXhUrpLnPaWkTCg8kGAb6LcKUVCG"
				, "AZTYKFkY3pJZiDQh7dFAfB9WntCfNEadVP"
				, "AZU6aU44XacnMArPXrCSrmFdd8X7VeZzDf"
				, "AZUfHVjf1LRtYEfKQUfJe8iCCKfbJSHcL3"
				, "AZUSa8dqxQ6mPqv6CudTSuzz2FyrVwDX4J"
				, "AZusyEotjv4zzU4XUqbxbBYwULMtDuWJvo"
				, "AZUUECmVkw6L13yYv8KRhXafevFgzAtqCx"
				, "AZV589uNciPqCoxa7gyAMQDHcR7NjVYNPg"
				, "AZVDrh1RNDNSh4ps1P2pEiF4rhwtN8npgR"
				, "AZvFX29D99iJtDyk73tuNPWMgq7x98J9F1"
				, "AZVJ36bcLiJJVZQY9eRjYU93Y9dxww8nYi"
				, "AZVPtfTA2JEHWSiUduj5aPwyWtsL7nS2eW"
				, "AZvUr2K8u9Yzap3qaHRchhiDd81tytu2sM"
				, "AZVVeNufPtaeRebjyWJfNnAit5ZbTBgd77"
				, "AZvxJNF1Lxkj1vEMijkL32KzsFiTkjB3yv"
				, "AZVZF5iKP9JJYu5EXpEHDjkfSjRfSUCqF4"
				, "AZW5jKmYWYh2NCUpy8taskqqtnGCd77RvH"
				, "AZW6G654QwAQ4eDSwduamCgQrxUpkzW2pM"
				, "AZW7F5CNSbVLnEpKoZWhZNNWLZttvsc1j7"
				, "AZWbeLFW3QbeFJs7RvryJqs8B5QJ2AbWnr"
				, "AZWi8rWxcUhZtwvQeUoo7tHUqDnGiabEGp"
				, "AZwjbUHqT5AYF5MeiRBcdHs48Dszv53xWi"
				, "AZWPPfTdpLURxxpTkPjE5WLaeD5Z6yqBMu"
				, "AZx6oB1vJjRd1BZJqbH3NuVoriVH5A4YDm"
				, "AZx9WLQYSjHBAzoLqz5gf5trRrBPvmUH3R"
				, "AZxazqYjgWurtxVTVjY3KdbhDAQmm5Bw5t"
				, "AZXGK4g7r3cS6UzmZjEVzQfju8aizGi38U"
				, "AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7"
				, "AZxraLEmwkZW2anr2YjzMWhnfXkZ7MrNeu"
				, "AZxrBXiYiMQWGahdb96w1RksvSn9gpN3dh"
				, "AZXZSYBJydg7RH1rB4ptasCxmftEZUvB96"
				, "AZxZT7mnAxUtWHjq4yKpkRSFeL2YToqLQ5"
				, "AZYcZAjLKLdc3LbiDByvPacsuHjMS7koro"
				, "AZydRHm5y4Rz1wRMAHEGvUbGAYqdXKDc3v"
				, "AZyFmSyH5RBGb9VWfSPbTvTsZMcrGTcBvi"
				, "AZyHaP1cLJsCijpfNLeX5s4F7D5cycLXNK"
				, "AZz8sPSS7GZ2VeFAKuzLZ7HZZ4xjtNeFdd"
				, "AZZDz8rkxeFxBHwX3jLrvXzaQ2HED9t5sR"
				, "AZZsyDrUdVDRgqeozn5XUSCzPVxwNqAF6d"
				, "AZZWEdsdBwLEYFhCqobwwrVi2r4dKHWmNc"
				, "AZZWYMqHzwPynpm46bEFRLMi8cGm25WYDa") == 0) {
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
                if (mapBlockIndex.count(hash (mapBlockIndex[hash]->nStatus & BLOCK_HAVE_DATA) == 0) {
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
