// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2014 The Bitcoin developers
// Copyright (c) 2019 Altebet.io / CCBC Team
// Developed by TFinch
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

#include <sstream>

#include <boost/algorithm/string/replace.hpp>
#include <boost/filesystem.hpp>
#include <boost/filesystem/fstream.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/thread.hpp>

using namespace boost;
using namespace std;

bool BadActor(const CTransaction& tx, CValidationState& state) {

	if (strcmp(addressSource.ToString().c_str(), "AeS8deM1XWh2embVkkTEJSABhT9sgEjDY7") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaBezQNQVt2jLmji8Nu3RMz5NFu2XxCbnv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaBXoKEHhjxEXGkE2NUymYg1SxZm1k1mfw") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Aae7h7dPHypikAQHC5mC5uFCxhmE6FQrUb") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AajgZNr39CLHG4hHtaB2kYp2qmssfnsdyJ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaLjTg7JT71gAbTDCxKvJYs5GAqnTWawYB") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaoiXuy7J82u32vhvGEMKfDRHUurwTWMWv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaoZ4etvzLaomVSJP18Cz9BpmyGNRZeUKC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AasnyCdas2qpckVixTNAuCoGmp9pibP9Mz") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AaUN23VJv6VNHbNfCcUqL8tjtc7nwwRkqC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AazmnoVLjE8ASJ1WeTq2znSQzNButy4HEU") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Ab9nJK67UgUwP1QGwpcuwv5oenRCytde4n") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AbE3H6NKSSBTwTs5BzR6TCbqVNRhdnnptt") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AbFMNnL2J8WLjvGM3JYvsncg7ECiYg8aod") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AbhfGWrCaUf6ZLpZBTvskd4phgAWAECUzv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Ac4PB1GDDFHxAc3LCWedNFwi6aXYqa9DJa") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Ac87xuLCknNGoeVeQbTBsooHveGB66wkQs") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Ac8dKdrZdtKLLuNWWTHB5iJYNcR7esuCEG") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Acj29Yi2XdZJtHjitbRN4wSSsD8qS4YHpY") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AcjPakjdnz4zHcP7HkhoRLg6vs95KwYhaR") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Acm3eowZLVY4XKn6t7EGmgAkfCE3saVvLG") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AcMeChtV6WyynHDk1U5Kgvk5YUGss7K5gy") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AcnQWshXPbuTxjqc49Ni5WPcbspR1TuBbF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Act5pUdqZcURMunSYM59xYxGPAEdENQH4o") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AcZajYwytuRdNz2BKLx1GDa22AJRCwGUBS") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AddMFE17HfmZYR3fubfo24dGmXkaRZNkBp") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdejZE713HDKovqr6G5uT31U6zja7KSyHS") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdePW7oHAqNH7d7apEj75yjWCpBgtwe7Tk") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdK6HZS2aTQeAbCrRdqu4NsdcNWsMX7nGx") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdNw5QtxBHKowKpG7kbRGm2en9Ci1pv6hA") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdQRLtsZoJNKSHyZYyhgFVHyWddoQgWXE5") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdTebzNJYasPXTe7QK5L8WdZnqruGhowaf") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AduHQy7XEbvvPVcv4UGfBA9o7W9kybWaeF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AdZn8Vcci1zQGVMdBb7afd8iW1cm9VXXeL") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AeCMNReq5TegieKpncZpx1NYwv5BohzVqz") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AehUQnCunEKfmAPsNsak72MjTpDz9qC3Kr") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AekVJg9Gv3recogGbRbBsP6eg81JDs5e5y") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AeL426qjTvixw7eLy9HgkYpuU2YUzA3uDS") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "Aeq4HBm453EwkFjxsWFjEwZm4gPmnv8vpF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AeRQZj9c6EhRgPrTq25ko2T3LfFDvGQv7C") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AeXBEKQ78B5ZUiZPqPTqGpyJK4NrFB1CNg") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AFuLVpZBHirH6Cw7VrPJA2p3rE5urDErsA") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGAe43Rc3yeJrqJ7XKT1J8bCVnstcn5F9T") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGbqULj2sNhnRqYLbjmgZRstYioHCMJ5Mi") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGDHCKBatYZNPkCZY58XhoKMqoineuLEdf") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGDky2wfk9zNDBEeujZED2GTxFexTkod3D") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGdo2isaBrQeFmGeC5Mn6Pds9zE8wX5DSe") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGgXnG5jgGuYCYg58fFM4vzcH5T6eEkzMH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGhXfmp1BDbtavNKWWGn8gy98Kvj9kLp1n") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGjkMQPPQyS9T2mpv1HF7GtSq2pV9czZLL") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGKAFaLW4i9H1WxaEDd43eEqDBqQ9drzp7") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGUGnWpBuuiUnAp1sxaJRMWERhGutrZK4e") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGv97VxVLWr7kfdFWZe5HSLvg28JwnyFKE") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGWijpgKPJq41Rf9PFxS2WEbR9c1TiohJe") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGx2dQUeHhUcLNYDk4ZvXHifPCqi6MapYN") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AGzdsw2LaGdML9jZaLbXXHw1dpwZ7tLfQk") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHHzxEcHK8a2cckjjdsB161YhRVDzqbfZm") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHm5J4KDdHxSZCJ2j3xGbgzYUFRRt9QE1H") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHMfzE7RREUHUAYXwdrUDfmTKB1o7HpN1C") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHnZ5hX9D4AShYZMupZkJLoLRBgWZbCn12") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHx6KDzxPUAhWn53QCZbMbYp43rN23949H") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AHZMq4xkmXd3MrqzCsTVVJZFu78tSuijnj") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJjFYKyHSMU2PNxt2btrxdGGV282FXHhUF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJMGWqkFYTQR3jFxNV1XDMbL6R6MGGdsUx") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJnCfE7XhE42Pm5qA66Hc9DuDQkk8NDVv6") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJNz9t3nsgGXQt9tYcVHbpVgD78Pfonra3") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJrjze3k76zuUWnptgwKnHaerFHjBqqYe4") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJw51w5ZcAxSx3F4szMx1sWB8SWt8GD7ME") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJwk6e8ZCyZi7vBaZriefajEMre6HJ8mMW") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AJyEVm3c4MnBwJpXdPvH9RgoHG61qnNCbr") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AK3RRQXBFT4e8feceLDm4BWMoQjj1rvJHh") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AK3zNgRYK8Fbu8Es4LKfNhMNRDQVUzEiQ4") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKC471thQfcpCUaBbP9dgxKZnkRsSuWdYY") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKHfvfWaYNb4A5rf67ECuXVcJD11ez1qxz") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKhJFMgTxSt3KNHSRqGJNPp91sEDMgXNgB") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKnHXiBz7Ww83AZ7LpzsFVAeFoSgUEsAHW") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKPLoYGFPR1qbCRjbNUSuoP2RU6tRqyYzK") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKs4uz7RE6zQqMLhrqDgy4cEjjDXkhT1ek") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKUuBtZGT8WVLpqyzTcj9UUnucRQvWNjVP") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AKyu17SjcztoYXEUMGysK7z929afyhSADX") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AL8fjjZZVJGMn3zwa6PL88keDuxwFnT6gR") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AL8SbHA1H8WyN1SoahXv3FESESLCgCctmU") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ALaE9sgtLjDAVBrXSd95SPsrwKvfDgZF1t") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ALhggXxrcqHUqdCXwSDjQWqHY34KYd6cMa") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ALHZ2Q4KVdsbwcDexCMuy3j4A3wYLNPYRU") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ALkPde6Xvcz9QPvBRpEEf8kmbdiZZd21aV") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMBW5kN11UiW7nedFjjLMBDQ2P34zA5uCe") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMFbKZVio92oRu8C6zPye8f9thFcuyjxys") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMfwTXNeoC1VWHVwn7QH8G6oiyUwU2fjFC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMJHVGNVbH6ASmL42fwDR8gWQ4F7PgSjHv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMKb6XhrsJiiGWQHvZrUed6Zm8qhvgHzut") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMxFbVWGWMW3DWTzhu215ft3KKybxWorCm") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AMYuDF9iSVwCazxk6sjEtRwedxYGJRqQLj") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AN5R5Y2tkKDiKv4XrQWAGFbVZJKnMW9MsV") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANCpo3RSUBTD1Ym2nfm7ic5YUXZbZcBGR7") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANfZ9zuKDxygghp3EmtBiPS2C2qj2SRxRD") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANjYLeqwqGz77kdzwUg3Mgeu8tDU2JYRxF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANKeNJVRfuehwdTgPnn9n9h5oz6pxPTCV1") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANmHzjKhXbvBcciyEbz5ArSEQRwMn1RXGs") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANMnQMuJUbV9Hy6X3dyXMkgdTBtCMvwDkC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANUkCbtNXkEdLVjChyd6bqZdnCRSDxcQXR") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANW1r76UqBibK5oQYH7GwgQJpHkGuqRM5F") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANxgPNkTg4RYBSjH7gM8M9wAkK4yB7SHws") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ANzYAGiwQEnQFcU1uVRSaQbybERC1Lg91J") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "APcnJAhHDdB4TE4muLH9ywwGei6sgikJJ3") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "APDJqZWCePYe9PV2Roo6LTePTFCmzmg2Ku") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "APdz8YkgEBzHeaCnT3xHgfhxvczToRBN63") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "APp8ruJuMs3sJT1GewK6uL1zV2D9ngPNUF") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "APwJSKvoLLYWW8fd1cTeP2BcC3wyByvUjo") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQ3rU7CFUg5f4kxarfZrPVu5jRYAqbSuL8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQAMJGidK4aXJV6EWh7H3JEuFs2XdBzZoM") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQDHrpq3pP6V78MWHLr7cj2sw8SQKtadKx") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQfHSwQjMi2eN8uPBh15yBVh2uHosq6VPd") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQFtdiQGzTP9JAP3F82qKpY4aDarXK8Hvo") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQhezkAmLaX3z2WUMwSQsDqMjRfmvyaj2u") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQhqqzSh6c6pe6KBbgomduQjiJ7Va6GF5B") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQTQmthD8g1EXU566kdgwoxYpDuVVEv2oN") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQVz4EuBsUN9sjtPzQGRA66wxeronZyz73") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AQW2wdHVU44uXeTBDDYhzHDGEsNvTKSQTb") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARaWFscUbQvfi8m1iftNuC9xt56FcYTQP8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARcQfBPbYqRs3PprDctXTyZoGx94uQr5bS") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARGb5i7MWxe69Me4EkvW5MTGvUnNB21YNY") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARHB1bFk9vnqpbfMTPTWsoxPpVeqjHsXCY") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARnndqPrxfHDK3mibW3uUvtiH9Y8SFnhrB") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ARoXfVzUw1At2EiHZzm7dUFLeAkR5DHuxM") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASA98WixLU7KRyYqBqNT2HbaeoBQqJjent") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASFh3ZSUMSmbv3i62F9Jy8YqhB3LYMJhkC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASgjfs4T1SgqJLzyd4P3Ywv8bcB6fS7UsQ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASJLEfixF4nCPCLBbjF9fEQhbPU6W7XJtX") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASKE6Uu1CuMFB88mUZpwRsfbpAqLfFG2uR") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ASZFN2nS7mvxLHQcuNsSHzTu6z8SrHMd16") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AT29ncRdDr8sKcHgKo1zYMmc51UuDZBZg2") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AT2koUKowQstHq5YE8FEdqDFXdDsrthRV9") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AT92sZHdwpWCbp2LEULpGEDeCAZNvpuNFj") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AT9undynPdpXJVhQQsfD9th68QBPJYkNTD") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATduFe5fgX8sdbrNNxcXDyFhTdsHbmaGCy") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATFL5Eb79CcNRJGb4hWmUuH3p7EDhKmSJX") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AThLPzKTuRTRmuyRn7SLKmg77b6oXHseDQ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATkP7Y7VmDYbGVjC3zGMJHtAUEFQeAwzJg") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATqsSQWxy8KsWsqR9aAUU9q85i8xhUHYJ6") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATrmatFVRQ3wUxntMrGJT5nyR3AUuZcpqQ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATxaEeKTJFMikNhDjTKSp9E5DXGA44DcbW") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "ATycywFh3iRLf4So4VV6XT8SftjFnVknaH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AU5hKjPdvDZhs5N3kJLSQMBA3UbrnE7VoC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUAVb9Tsk7zNjb4v1d67QBWmFurdivSjic") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUdD18nERTTDhQUfM6VWnJjnkWu76wxnpa") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUgdTHjGRpStx8Mwy7FHRg3HTu6G5fJhaB") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUjPFoWz76T2Gz38mMnHu5EudvfDN41J1x") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUjtqZK7RQstx4Q3RnZL9ybCMmRdwM5Fep") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUNfopFXpj2WxgBcEKAavQ8XRw9LhPvDPw") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AUVNg586VuvoC142FvKG4iteuL7aCikViA") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AV9fyQgWHJGYCYZ4QJVvYNRe6YrSTwsDB4") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVb11DsuwQu4oW4LoVndqA5WyskEGxpLeb") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVb6QL19jFy5hFQJtuHoGwuYbNWpxBHAsQ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVgMXp3s8HU9aziUfi7HhVc6rCKsLc46nC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVgYxGQidDnYYQJEGsYrEqdj3y2BTe4PL1") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVpxB7fDYCFgLV9MJ4LcWYxPyeEaFFU8RX") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVQqyFT7CBSsQEeGSjxmsHoFRXU5PwHjbj") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVRXBRQh5iJPw4cjgNZ7LH97gHxyxaxnJv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVt15fH21QcDkpkf75pmmoebenjhXu8om2") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVt1hffz3n3vLAFd5YF7X8iEx58GxJFim1") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVYdvRn58wNqW8JUSk1gugVda5D2iSRZGG") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AVzPqbjRGYitxahoFwgj6VBNBWfYgUBdUy") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AW4K2vE48phZcbuZ9LbJSpuGDosGrK6UXH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWa5hjMvPjBgoc8Kivpuc4gZfqCjVexzFH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWaLekM34R2sfV5tMa5j7SJnFAE6RHjk3d") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWecrxwNbskTSopQw91V5ybkVVHK6F4axP") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWF2UReo78ZsK8HuoeDhhFQZmWhrkLCA5y") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWfXPwUYuLYcLtjJEiTXe8L3Ffk2PfVMC6") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWRbrSw1t41YSQPMLjh3aaaDna8fW3VXUj") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AWVvb1zCjfFCBVSMScTLJVubFmTXZxSXus") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AX3bQwmuo6mDK8qtNJXPCciAgNcbU7vfqQ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AX4gK27amGhzkwJ1ufBi63BMNEBtaYCqs8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AX9rPK142J4YdreEbXWp939fCX3xxzSTK8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXCVvFMqm8kBjZaEFjh6HqjrogSxo5iu4J") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXE41XcLVrkzpKE5S5L9ZFXAbvRHvTkZjC") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXfqTAptfVG6Szz5KnC13VB1giXxHUWz4k") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXG8pPkDWhxA1HNNEnfG5umWiJ3aDvUfpv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXJW7yE8qZ3shEEFbtaDmbtgsxgWvP7dhN") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXmGZLTMnnmyEhaut6ynXUNR7y1b8HN7gh") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXmwZqJJG2iTi9YA8xH1M6jpuzJbP6ZSG8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXRA3e5gwYkvVhUNmHJscpvvrrzrL5jMZY") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXTtN8bMRVKmtd7Ft39NTkNUd56v3VhPjv") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXuzGycTq567gfVFfDChUU3ZnGv1Mu3GDH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AXyUBv19Lb8fZN7vDbcK1ga35TiyncTGzE") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AY9N2FDJ3YTiQFen5Cr5fcecUwyhehmERJ") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYbKUxJa3kyTgpvtKWzBcSxUEnKSUkY3FN") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYbXimKftwveeRGoweEcaCZHYSC9iZWUBK") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYJEjYeUnp2v8CLJq4nSZVdWL69ixUhaW1") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYkiEZuJXwUaKwyirNGbtqa5XMA3xcuBd7") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYnnqRb8zPnAzEgr4G1ppbDFsnmNUX2sA8") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYVP9PQzrTdU4h9v2pmRsXZCyVZKn3onGH") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYZPE24DsuQPb2YxWNnrxpSYQMGgAeRnMi") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AYZZfKpopxvtwxENx68gKH3oZM7NbmeSRE") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZASSeJFzvrxWYotoiXucm7ruBUrRdV4n3") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZcFmwJAoDg2EJA1KjNk3NFMfn4ZnafpYm") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZdXqASf7C4iJY2YKnrMvP6xi94kpD4ZiL") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZGCZ7c1GrntN8udyNL8t2ed6dgNCYpuPP") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZJyMQYhstsr7p4BLde6SsrKpJ7NKMAhdx") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZoQSSvg2jcdD3Cdy6fMZFndbs33qT3Fo4") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZqFXJeDqGDkPnKFs6hnrLUGynqLzv6yVo") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
	else if (strcmp(addressSource.ToString().c_str(), "AZXLwnDyzDA1HvaVK3qJseopJQw43vmFa7") == 0) {
		return state.DoS(100, false, REJECT_INVALID, "bad-txns-inputs-premine");
	}
}