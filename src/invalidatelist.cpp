// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Copyright (c) 2019 Altbet.io / CCBC Team
// Developed by TFinch / Aviator
//  
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "main.h"
#include "invalidatelist.h"
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
#include <vector>
#include <algorithm>
#include <sstream>
#include <boost/algorithm/string/replace.hpp>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/thread.hpp>

using namespace boost;
using namespace std;

/*
bool BadActor(const CTransaction& tx, CValidationState& state) {
	switch (addressSource) {
	//switch (addressSource.ToString().c_str()) {
case 'AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7':
	case 'AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv':
	case 'AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw':
	case 'Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb':
	case 'AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ':
	case 'AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB':
	case 'AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv':
	case 'AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC':
	case 'AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz':
	case 'AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC':
	case 'AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU':
	case 'Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n':
	case 'AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt':
	case 'AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod':
	case 'AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv':
	case 'Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa':
	case 'Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs':
	case 'Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG':
	case 'Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY':
	case 'AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR':
	case 'Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG':
	case 'AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy':
	case 'AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF':
	case 'Act5pUdqZcURMunSYM59xYxGPAEdENQH4o':
	case 'AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS':
	case 'AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp':
	case 'AdejZE713HDKovqr6G5uT31U6zja7KSyHS':
	case 'AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk':
	case 'AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx':
	case 'AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA':
	case 'AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5':
	case 'AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf':
	case 'AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF':
	case 'AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL':
	case 'AeCMNReq5TegieKpncZpx1NYwv5BohzVqz':
	case 'AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr':
	case 'AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y':
	case 'AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS':
	case 'Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF':
	case 'AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C':
	case 'AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg':
	case 'AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA':
	case 'AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T':
	case 'AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi':
	case 'AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf':
	case 'AGDky2wfk9zNDBEeujZED2GTxFexTkod3D':
	case 'AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe':
	case 'AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH':
	case 'AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n':
	case 'AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL':
	case 'AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7':
	case 'AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e':
	case 'AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE':
	case 'AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe':
	case 'AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN':
	case 'AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk':
	case 'AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm':
	case 'AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H':
	case 'AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C':
	case 'AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12':
	case 'AHx6KDzxPUAhWn53QCZbMbYp43rN23949H':
	case 'AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj':
	case 'AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF':
	case 'AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx':
	case 'AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6':
	case 'AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3':
	case 'AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4':
	case 'AJw51w5ZcAxSx3F4szMx1sWB8SWt8GD7ME':
	case 'AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW':
	case 'AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr':
	case 'AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh':
	case 'AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4':
	case 'AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY':
	case 'AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz':
	case 'AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB':
	case 'AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW':
	case 'AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK':
	case 'AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek':
	case 'AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP':
	case 'AKyu17SjcztoYXEUMGysK7z929afyhSADX':
	case 'AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR':
	case 'AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU':
	case 'ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t':
	case 'ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa':
	case 'ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU':
	case 'ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV':
	case 'AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe':
	case 'AMFbKZVio92oRu8C6zPye8f9thFcuyjxys':
	case 'AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC':
	case 'AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv':
	case 'AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut':
	case 'AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm':
	case 'AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj':
	case 'AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV':
	case 'ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7':
	case 'ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD':
	case 'ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF':
	case 'ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1':
	case 'ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs':
	case 'ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC':
	case 'ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR':
	case 'ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F':
	case 'ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws':
	case 'ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J':
	case 'APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3':
	case 'APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku':
	case 'APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63':
	case 'APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF':
	case 'APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo':
	case 'AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8':
	case 'AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM':
	case 'AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx':
	case 'AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd':
	case 'AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo':
	case 'AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u':
	case 'AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B':
	case 'AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN':
	case 'AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73':
	case 'AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb':
	case 'ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8':
	case 'ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS':
	case 'ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY':
	case 'ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY':
	case 'ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB':
	case 'ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM':
	case 'ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent':
	case 'ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC':
	case 'ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ':
	case 'ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX':
	case 'ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR':
	case 'ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16':
	case 'AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2':
	case 'AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9':
	case 'AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj':
	case 'AT9undynPdpXJVhQQsfD9th68QBPJYkNTD':
	case 'ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy':
	case 'ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX':
	case 'AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ':
	case 'ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg':
	case 'ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6':
	case 'ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ':
	case 'ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW':
	case 'ATycywFh3iRLf4So4VV6XT8SftjFnVknaH':
	case 'AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC':
	case 'AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic':
	case 'AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa':
	case 'AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB':
	case 'AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x':
	case 'AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep':
	case 'AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw':
	case 'AUVNg586VuvoC142FvKG4iteuL7aCikViA':
	case 'AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4':
	case 'AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb':
	case 'AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ':
	case 'AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC':
	case 'AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1':
	case 'AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX':
	case 'AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj':
	case 'AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv':
	case 'AVt15fH21QcDkpkf75pmmoebenjhXu8om2':
	case 'AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1':
	case 'AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG':
	case 'AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy':
	case 'AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH':
	case 'AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH':
	case 'AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d':
	case 'AWecrxwNbskTSopQw91V5ybkVVHK6F4axP':
	case 'AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y':
	case 'AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6':
	case 'AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj':
	case 'AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus':
	case 'AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ':
	case 'AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8':
	case 'AX9rPK142J4YdreEbXWp939fCX3xxzSTK8':
	case 'AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J':
	case 'AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC':
	case 'AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k':
	case 'AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv':
	case 'AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN':
	case 'AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh':
	case 'AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8':
	case 'AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY':
	case 'AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv':
	case 'AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH':
	case 'AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE':
	case 'AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ':
	case 'AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN':
	case 'AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK':
	case 'AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1':
	case 'AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7':
	case 'AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8':
	case 'AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH':
	case 'AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi':
	case 'AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE':
	case 'AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3':
	case 'AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm':
	case 'AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL':
	case 'AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP':
	case 'AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx':
	case 'AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4':
	case 'AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo':
	case 'AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7':
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
		break;
	}
}*/

bool BadActor(const CTransaction& tx, CValidationState& state) {
{
	vector<string> BadNodes;
	BadNodes.push_back("AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7");
	BadNodes.push_back("AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv");
	BadNodes.push_back("AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw");
	BadNodes.push_back("Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb");
	BadNodes.push_back("AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ");
	BadNodes.push_back("AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB");
	BadNodes.push_back("AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv");
	BadNodes.push_back("AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC");
	BadNodes.push_back("AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz");
	BadNodes.push_back("AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC");
	BadNodes.push_back("AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU");
	BadNodes.push_back("Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n");
	BadNodes.push_back("AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt");
	BadNodes.push_back("AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod");
	BadNodes.push_back("AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv");
	BadNodes.push_back("Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa");
	BadNodes.push_back("Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs");
	BadNodes.push_back("Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG");
	BadNodes.push_back("Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY");
	BadNodes.push_back("AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR");
	BadNodes.push_back("Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG");
	BadNodes.push_back("AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy");
	BadNodes.push_back("AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF");
	BadNodes.push_back("Act5pUdqZcURMunSYM59xYxGPAEdENQH4o");
	BadNodes.push_back("AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS");
	BadNodes.push_back("AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp");
	BadNodes.push_back("AdejZE713HDKovqr6G5uT31U6zja7KSyHS");
	BadNodes.push_back("AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk");
	BadNodes.push_back("AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx");
	BadNodes.push_back("AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA");
	BadNodes.push_back("AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5");
	BadNodes.push_back("AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf");
	BadNodes.push_back("AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF");
	BadNodes.push_back("AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL");
	BadNodes.push_back("AeCMNReq5TegieKpncZpx1NYwv5BohzVqz");
	BadNodes.push_back("AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr");
	BadNodes.push_back("AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y");
	BadNodes.push_back("AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS");
	BadNodes.push_back("Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF");
	BadNodes.push_back("AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C");
	BadNodes.push_back("AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg");
	BadNodes.push_back("AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA");
	BadNodes.push_back("AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T");
	BadNodes.push_back("AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi");
	BadNodes.push_back("AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf");
	BadNodes.push_back("AGDky2wfk9zNDBEeujZED2GTxFexTkod3D");
	BadNodes.push_back("AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe");
	BadNodes.push_back("AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH");
	BadNodes.push_back("AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n");
	BadNodes.push_back("AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL");
	BadNodes.push_back("AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7");
	BadNodes.push_back("AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e");
	BadNodes.push_back("AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE");
	BadNodes.push_back("AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe");
	BadNodes.push_back("AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN");
	BadNodes.push_back("AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk");
	BadNodes.push_back("AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm");
	BadNodes.push_back("AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H");
	BadNodes.push_back("AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C");
	BadNodes.push_back("AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12");
	BadNodes.push_back("AHx6KDzxPUAhWn53QCZbMbYp43rN23949H");
	BadNodes.push_back("AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj");
	BadNodes.push_back("AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF");
	BadNodes.push_back("AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx");
	BadNodes.push_back("AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6");
	BadNodes.push_back("AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3");
	BadNodes.push_back("AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4");
	BadNodes.push_back("AJw51w5ZcAxSx3F4szMx1sWB8SWt8GD7ME");
	BadNodes.push_back("AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW");
	BadNodes.push_back("AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr");
	BadNodes.push_back("AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh");
	BadNodes.push_back("AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4");
	BadNodes.push_back("AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY");
	BadNodes.push_back("AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz");
	BadNodes.push_back("AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB");
	BadNodes.push_back("AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW");
	BadNodes.push_back("AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK");
	BadNodes.push_back("AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek");
	BadNodes.push_back("AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP");
	BadNodes.push_back("AKyu17SjcztoYXEUMGysK7z929afyhSADX");
	BadNodes.push_back("AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR");
	BadNodes.push_back("AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU");
	BadNodes.push_back("ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t");
	BadNodes.push_back("ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa");
	BadNodes.push_back("ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU");
	BadNodes.push_back("ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV");
	BadNodes.push_back("AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe");
	BadNodes.push_back("AMFbKZVio92oRu8C6zPye8f9thFcuyjxys");
	BadNodes.push_back("AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC");
	BadNodes.push_back("AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv");
	BadNodes.push_back("AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut");
	BadNodes.push_back("AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm");
	BadNodes.push_back("AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj");
	BadNodes.push_back("AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV");
	BadNodes.push_back("ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7");
	BadNodes.push_back("ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD");
	BadNodes.push_back("ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF");
	BadNodes.push_back("ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1");
	BadNodes.push_back("ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs");
	BadNodes.push_back("ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC");
	BadNodes.push_back("ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR");
	BadNodes.push_back("ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F");
	BadNodes.push_back("ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws");
	BadNodes.push_back("ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J");
	BadNodes.push_back("APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3");
	BadNodes.push_back("APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku");
	BadNodes.push_back("APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63");
	BadNodes.push_back("APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF");
	BadNodes.push_back("APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo");
	BadNodes.push_back("AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8");
	BadNodes.push_back("AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM");
	BadNodes.push_back("AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx");
	BadNodes.push_back("AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd");
	BadNodes.push_back("AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo");
	BadNodes.push_back("AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u");
	BadNodes.push_back("AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B");
	BadNodes.push_back("AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN");
	BadNodes.push_back("AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73");
	BadNodes.push_back("AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb");
	BadNodes.push_back("ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8");
	BadNodes.push_back("ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS");
	BadNodes.push_back("ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY");
	BadNodes.push_back("ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY");
	BadNodes.push_back("ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB");
	BadNodes.push_back("ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM");
	BadNodes.push_back("ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent");
	BadNodes.push_back("ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC");
	BadNodes.push_back("ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ");
	BadNodes.push_back("ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX");
	BadNodes.push_back("ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR");
	BadNodes.push_back("ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16");
	BadNodes.push_back("AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2");
	BadNodes.push_back("AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9");
	BadNodes.push_back("AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj");
	BadNodes.push_back("AT9undynPdpXJVhQQsfD9th68QBPJYkNTD");
	BadNodes.push_back("ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy");
	BadNodes.push_back("ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX");
	BadNodes.push_back("AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ");
	BadNodes.push_back("ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg");
	BadNodes.push_back("ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6");
	BadNodes.push_back("ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ");
	BadNodes.push_back("ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW");
	BadNodes.push_back("ATycywFh3iRLf4So4VV6XT8SftjFnVknaH");
	BadNodes.push_back("AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC");
	BadNodes.push_back("AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic");
	BadNodes.push_back("AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa");
	BadNodes.push_back("AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB");
	BadNodes.push_back("AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x");
	BadNodes.push_back("AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep");
	BadNodes.push_back("AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw");
	BadNodes.push_back("AUVNg586VuvoC142FvKG4iteuL7aCikViA");
	BadNodes.push_back("AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4");
	BadNodes.push_back("AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb");
	BadNodes.push_back("AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ");
	BadNodes.push_back("AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC");
	BadNodes.push_back("AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1");
	BadNodes.push_back("AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX");
	BadNodes.push_back("AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj");
	BadNodes.push_back("AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv");
	BadNodes.push_back("AVt15fH21QcDkpkf75pmmoebenjhXu8om2");
	BadNodes.push_back("AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1");
	BadNodes.push_back("AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG");
	BadNodes.push_back("AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy");
	BadNodes.push_back("AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH");
	BadNodes.push_back("AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH");
	BadNodes.push_back("AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d");
	BadNodes.push_back("AWecrxwNbskTSopQw91V5ybkVVHK6F4axP");
	BadNodes.push_back("AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y");
	BadNodes.push_back("AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6");
	BadNodes.push_back("AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj");
	BadNodes.push_back("AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus");
	BadNodes.push_back("AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ");
	BadNodes.push_back("AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8");
	BadNodes.push_back("AX9rPK142J4YdreEbXWp939fCX3xxzSTK8");
	BadNodes.push_back("AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J");
	BadNodes.push_back("AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC");
	BadNodes.push_back("AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k");
	BadNodes.push_back("AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv");
	BadNodes.push_back("AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN");
	BadNodes.push_back("AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh");
	BadNodes.push_back("AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8");
	BadNodes.push_back("AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY");
	BadNodes.push_back("AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv");
	BadNodes.push_back("AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH");
	BadNodes.push_back("AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE");
	BadNodes.push_back("AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ");
	BadNodes.push_back("AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN");
	BadNodes.push_back("AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK");
	BadNodes.push_back("AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1");
	BadNodes.push_back("AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7");
	BadNodes.push_back("AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8");
	BadNodes.push_back("AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH");
	BadNodes.push_back("AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi");
	BadNodes.push_back("AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE");
	BadNodes.push_back("AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3");
	BadNodes.push_back("AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm");
	BadNodes.push_back("AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL");
	BadNodes.push_back("AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP");
	BadNodes.push_back("AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx");
	BadNodes.push_back("AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4");
	BadNodes.push_back("AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo");
	BadNodes.push_back("AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7");


	//If Bad node Return true
	if (std::find(BadNodes.begin(), BadNodes.end(), address) != BadNodes.end()) {
		return true || state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");;
	}

	//If Nothing else return False
	return false;
}