#!/usr/bin/env python3
"""Independent exact checker; does not import verify.py.

Uses Stirling numbers for biclique counts, transfer recurrences for cycle
counts, and dynamic programming for maximum products of integer partitions.
Checks the delivered finite proof certificate and independently extends it.
"""
from __future__ import annotations
import csv
import json
import platform
from functools import lru_cache
from math import factorial, gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


@lru_cache(None)
def S(n: int, k: int) -> int:
    if n == 0:
        return int(k == 0)
    if k <= 0 or k > n:
        return 0
    return k * S(n-1,k) + S(n-1,k-1)


@lru_cache(None)
def B(a: int, b: int) -> int:
    return sum(factorial(4) // factorial(4-i) * S(a,i) * (4-i) ** b
               for i in range(1, min(4,a)+1))


@lru_cache(None)
def C(length: int) -> int:
    same, different = 1, 0
    for _ in range(1,length):
        same, different = different, 3 * same + 2 * different
    return 4 * different


def run() -> dict:
    endpoint = 100
    J = [1]
    for r in range(1,endpoint+1):
        J.append(max(part * J[r-part] for part in range(1,r+1)))
    source = ROOT / "data" / "base_certificate.csv"
    with source.open(newline="", encoding="utf-8") as handle:
        saved = {int(row["n"]): row for row in csv.DictReader(handle)}
    check(set(saved) == set(range(7,26)), "Finite certificate has the wrong range")
    total = base = 0
    for n in range(7,endpoint+1):
        A = max(j for j in range(1,n//2+1) if gcd(j,n-j) == 1)
        target = B(A,n-A) - A*(n-A)
        q,z = divmod(n,4)
        orbit_max = factorial(n) // (factorial(q) ** (4-z) * factorial(q+1) ** z)
        vals = [(4**n-3**n, "nonsurjective"),
                (4**n-orbit_max, "two_permutations"),
                (9*4**(n-2)-1, "two_singular")]
        for m in range(2,n+1):
            for length in range(2,m+1):
                if m % length == 0:
                    d,r = m//length,n-m
                    vals.append((C(length)**d * 4**r - m*J[r], f"cycle;{m};{d};{r}"))
        # Sum-first enumeration, rather than the primary checker's a-first enumeration.
        for occupied in range(2,n+1):
            r = n-occupied
            for a in range(1,occupied//2+1):
                b = occupied-a
                d = gcd(a,b)
                vals.append((B(a//d,b//d)**d * 4**r - (a*b//d)*J[r],
                             f"cross;{a};{b};{d};{r}"))
        vals.sort()
        check(vals[0] == (target,f"cross;{A};{n-A};1;0"), f"Independent minimum failed at {n}")
        check(vals[1][0] > target, f"Independent uniqueness failed at {n}")
        if n in saved:
            row = saved[n]
            for key,value in (("A",A),("B",n-A),("deficit",target),
                              ("maximum",4**n-target),("margin",vals[1][0]-target),
                              ("candidates",len(vals))):
                check(int(row[key]) == value, f"Certificate disagreement: n={n}, key={key}")
            check(row["runner_up"] == vals[1][1], f"Runner-up disagreement at {n}")
            base += len(vals)
        total += len(vals)
    report = dict(status="PASS", python=platform.python_version(),
                  independently_checked_range=[7,endpoint], candidates=total,
                  certificate_range=[7,25], certificate_candidates=base,
                  formulas="Stirling DP; cycle transfer; integer-partition product DP",
                  imports_primary_checker=False, assertion_independent=True)
    (ROOT / "data" / "independent_check.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    return report


if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
