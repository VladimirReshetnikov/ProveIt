#!/usr/bin/env python3
"""Optional finite discovery experiment, independent of the universal proof.

Enumerate templates with k singleton entries, record reversal-pair supports,
and search for separating templates with contained support. Python 3.10+;
standard library only. Patterns in this exploratory script are zero-based.
The production constructor in reverse_reply.py is one-based.
"""
from __future__ import annotations
import argparse
import json
import time
from itertools import combinations, permutations
from pathlib import Path


def standardize(s):
    ranks = {v: i for i, v in enumerate(sorted(s))}
    return tuple(ranks[x] for x in s)


def inflate(beta, index, t, sign):
    v = beta[index]
    out = []
    for j, x in enumerate(beta):
        if j == index:
            out.extend(range(v, v+t) if sign == 1 else range(v+t-1, v-1, -1))
        else:
            out.append(x if x < v else x+t-1)
    return tuple(out)


def explore(k: int, include_witnesses: bool = False) -> dict:
    start = time.monotonic()
    pats = list(permutations(range(k)))
    pid = {p: i for i, p in enumerate(pats)}
    pairs = sorted({min(p, p[::-1]) for p in pats})
    mono = pairs.index(tuple(range(k)))
    witnesses = {}
    count = 0
    for beta in permutations(range(k+1)):
        for i in range(k+1):
            other = tuple(j for j in range(k+1) if j != i)
            for sign in (1, -1):
                shadow = 0
                for t in range(k+1):
                    for choice in combinations(other, k-t):
                        if t == 0:
                            p = standardize(tuple(beta[j] for j in choice))
                        else:
                            ix = sorted(choice + (i,))
                            p = inflate(standardize(tuple(beta[j] for j in ix)),
                                        ix.index(i), t, sign)
                        shadow |= 1 << pid[p]
                witnesses.setdefault(shadow, (beta, i, sign))
                count += 1
    bysupport = {}
    for shadow in witnesses:
        support = separable = 0
        for a, p in enumerate(pairs):
            b, c = (shadow >> pid[p]) & 1, (shadow >> pid[p[::-1]]) & 1
            if b or c: support |= 1 << a
            if b != c: separable |= 1 << a
        support &= ~(1 << mono)
        separable &= ~(1 << mono)
        bysupport[support] = bysupport.get(support, 0) | separable
    failed = []
    for support in sorted(bysupport, key=lambda s: (s.bit_count(), s)):
        separable = bysupport[support]
        if support & ~separable:
            for small, sep in bysupport.items():
                if small & ~support == 0:
                    separable |= sep
                if support & ~separable == 0:
                    break
        missing = support & ~separable
        if missing:
            failed.append({"support": str(support), "missing": str(missing)})
    out = {"k": k, "templates_checked": count, "distinct_shadows": len(witnesses),
           "distinct_supports": len(bysupport), "bad": failed,
           "elapsed_seconds": round(time.monotonic() - start, 3),
           "scope": "finite fixed-k exploration; not a proof of the universal theorem"}
    if include_witnesses:
        out["witnesses"] = [{"shadow": str(sh), "beta_zero_based": list(w[0]),
                             "marked_index_zero_based": w[1], "sign": w[2]}
                            for sh, w in witnesses.items()]
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--k", type=int, choices=range(3, 7), default=5)
    parser.add_argument("--witnesses", action="store_true",
                        help="Also record all distinct-shadow witnesses (larger JSON)")
    args = parser.parse_args()
    out = explore(args.k, args.witnesses)
    root = Path(__file__).resolve().parents[1]
    (root / "data").mkdir(exist_ok=True)
    target = root / "data" / f"exploration_k{args.k}.json"
    target.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k != "witnesses"}, indent=2))
    print("Wrote", target)

if __name__ == "__main__":
    main()
