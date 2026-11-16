#!/usr/bin/env python3
"""Mutation testing of the Verity Safe: each mutant breaks one security-relevant line of
Safe/Contract.lean; the Foundry suite must fail on every mutant ("killed").

Usage: scripts/mutate.py [--json] [NAME ...]   (default: all mutants)
Prints one line per surviving mutant; exit 1 if any survives. --json prints all results.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "Safe" / "Contract.lean"

MUTANTS: dict[str, tuple[str, str]] = {
    "no-nonce-increment": ("setStorage nonceSlot (add n 1)", "setStorage nonceSlot n"),
    "nonce-not-hashed": ("mstore (add p 320) n", "mstore (add p 320) 0"),
    "owner-order-nonstrict": ("currentOwner > lastOwner", "currentOwner >= lastOwner"),
    "owner-order-not-tracked": ("lastOwner := currentOwner)", "lastOwner := 0)"),
    "loop-one-short": ('forEach "i" t (do', 'forEach "i" (sub t 1) (do'),
    "not-owner-accepted": ("isOwnerWord != 0", "isOwnerWord == isOwnerWord"),
    "sentinel-accepted": ("currentOwner != sentinel) \"GS026\"", "true) \"GS026\""),
    "approval-unchecked": ("addressToWord sender == currentOwner || approved != 0", "true"),
    "ethsign-no-v-adjust": ("ecrecover prefixed (sub v 4) r s", "ecrecover prefixed v r s"),
    "ethsign-no-prefix": ("ecrecover prefixed (sub v 4) r s", "ecrecover txHash (sub v 4) r s"),
    "sig-length-unchecked": ("require (sigLen >= staticPart) \"GS020\"", "require (sigLen >= 0) \"GS020\""),
    "1271-magic-unchecked": ("require (magic == eip1271Magic) \"GS024\"", "require (true) \"GS024\""),
    "1271-pointer-unchecked": ("require (s >= staticPart) \"GS021\"", "require (true) \"GS021\""),
    "gs013-dropped": ("require (success == 1 || safeTxGas != 0 || gasPrice_ != 0) \"GS013\"", "pure ()"),
    "delegatecall-as-call": ("if operation == 1 then\n      success := delegatecall", "if operation == 2 then\n      success := delegatecall"),
    "eth-refund-price-unbounded": ("let price := min gasPrice_ txPrice", "let price := gasPrice_"),
    "refund-receiver-ignored": ("addressToWord txSender else addressToWord refundReceiver", "addressToWord txSender else addressToWord txSender"),
    "gs010-dropped": ('require (g0 >= add (max (div (mul safeTxGas 64) 63) (add safeTxGas 2500)) 500) "GS010"', "pure ()"),
    "setup-duplicate-allowed": ('require (existing == 0) "GS204"', 'require (true) "GS204"'),
    "setup-threshold-unbounded": ('require (_threshold <= n) "GS201"', 'require (true) "GS201"'),
    "approvehash-anyone": ('require (o != 0) "GS030"', 'require (true) "GS030"'),
}


def run(cmd: list[str]) -> bool:
    return subprocess.run(cmd, cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("names", nargs="*", help="mutants to run (default: all)")
    ap.add_argument("--json", action="store_true", help="print every result as JSON")
    args = ap.parse_args()
    names = args.names or list(MUTANTS)
    original = SRC.read_text()
    results: dict[str, str] = {}
    try:
        for name in names:
            old, new = MUTANTS[name]
            if original.count(old) != 1:
                results[name] = "stale"  # the mutant no longer matches the source exactly once
                continue
            SRC.write_text(original.replace(old, new))
            if not run(["scripts/build.sh"]):
                results[name] = "killed-by-build"
            elif not run(["forge", "test"]):
                results[name] = "killed"
            else:
                results[name] = "survived"
    finally:
        SRC.write_text(original)
        run(["scripts/build.sh"])
    if args.json:
        print(json.dumps(results, indent=2))
    else:
        for name, verdict in results.items():
            if verdict in ("survived", "stale"):
                print(f"{verdict}: {name}")
    return 0 if all(v.startswith("killed") for v in results.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
