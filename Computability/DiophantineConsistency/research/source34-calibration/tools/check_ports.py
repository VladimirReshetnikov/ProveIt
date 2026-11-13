"""Check the digit-list forms of the source34 masks used by Source34Ports.

Usage: py -I -X utf8 -S -B check_ports.py

`Source34Ports` defines the masks as digit lists in radix 2^121:

* MC is `CompactListMask.digits (2^121) 8801 1063 (E minus {1})`. Its digits
  are B-4 at the special cell 1063, B-2 on the support and B-1 elsewhere.
* MF_native is the explicit list `highDigits` below.

This script rebuilds both integers from those lists and compares them with the
package payloads `MC.bin.gz` and `MF_source.bin.gz`, where
MF_source = MF_native + beta. It is finite external evidence for the
transcription, not a Lean theorem.
"""
import gzip
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
PKG = ROOT / "candidates/valuation-shared-norms/source/inherited/root_fusion/coefficients"

RHO_BITS, L = 121, 8801
RHO = 1 << RHO_BITS
E = (list(range(943)) + list(range(960, 1040, 2))
     + [1063, 1064, 1095, 1096, 2195, 3296])
MU = 1022 + sum(1 << (10 + 2 * j) for j in range(44))
PAD = (1 << 119) - 1
LAST = (1 << 27) - 1


def high_digits():
    rep = lambda n, x: [x] * n
    track = [1, 0] * 10
    return ([4] + rep(999, 0) + track + [0] + track + rep(1154, 0)
            + [1] + rep(1100, 0) + [1] + rep(1096, 0) + [MU] + rep(1101, 0) + [MU]
            + rep(3296, 0) + rep(7, PAD) + [LAST, 0])


def low_digits():
    support = set(E) - {1}
    return [RHO - 4 if j == 1063 else RHO - 2 if j in support else RHO - 1
            for j in range(L)]


def of_digits(ds):
    v = 0
    for d in reversed(ds):
        v = v * RHO + d
    return v


def payload(name):
    return int.from_bytes(gzip.open(PKG / name).read(), "little")


def main():
    hd, ld = high_digits(), low_digits()
    beta = (1 << (RHO_BITS * L)) - 1
    ok = len(hd) == L and len(ld) == L and all(d < RHO for d in hd + ld)
    print(f"lengths {len(hd)}, {len(ld)}; digits below 2^121: {ok}")
    mc = of_digits(ld) == payload("MC.bin.gz")
    mf = of_digits(hd) + beta == payload("MF.bin.gz")
    print(f"MC from digit list matches payload: {mc}")
    print(f"MF_native + beta from digit list matches MF payload: {mf}")
    ok = ok and mc and mf
    print("ok" if ok else "MISMATCH")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
