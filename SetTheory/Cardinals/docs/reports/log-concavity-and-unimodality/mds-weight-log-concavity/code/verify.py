#!/usr/bin/env python3
"""Reproduce the exact checks in the article. Python 3.9+, no dependencies.

Run from this directory:
  python verify.py --max-n 200 --output ../data/verification.json

The large parameter sweep tests FORMAL enumerators, not code existence.
The separately reported enumeration tests construct actual small codes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import time
from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
from mds import failures, prediction, twice_quadratic, weights, weights_inclusion_exclusion


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def gf4mul(a: int, b: int) -> int:
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 4:
            a ^= 7  # X^2+X+1
        b >>= 1
    return result


def enumerate_rs(p: int, n: int, k: int) -> list[int]:
    a = [0] * (n + 1)
    for coefficients in product(range(p), repeat=k):
        w = 0
        for x in range(n):
            y = 0
            for c in reversed(coefficients):
                y = (y * x + c) % p
            w += y != 0
        a[w] += 1
    return a


def enumerate_parity(q: int, n: int) -> list[int]:
    a = [0] * (n + 1)
    for prefix in product(range(q), repeat=n - 1):
        if q == 4:
            last = 0
            for x in prefix:
                last ^= x
        else:
            last = (-sum(prefix)) % q
        a[sum(x != 0 for x in prefix) + (last != 0)] += 1
    return a


def enumerate_hexacode() -> list[int]:
    g = [(1, 0, 0, 1, 1, 1), (0, 1, 0, 1, 2, 3), (0, 0, 1, 1, 3, 2)]
    a = [0] * 7
    for m in product(range(4), repeat=3):
        word = [0] * 6
        for r in range(3):
            for c in range(6):
                word[c] ^= gf4mul(m[r], g[r][c])
        a[sum(x != 0 for x in word)] += 1
    return a


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=200)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    require(args.max_n >= 10, "max-n must be at least 10")
    start = time.monotonic()
    counts = {"q_greater_than_d": 0, "q_equals_d_ge_3": 0,
              "binary_boundary": 0, "degenerate": 0,
              "independent_formula": 0, "rational_defect_bound": 0,
              "actual_code_enumerations": 0, "actual_codewords": 0}
    digest = hashlib.sha256()

    # The same exact deterministic sweep reported in the article.
    for n in range(4, args.max_n + 1):
        for d in range(2, n - 1):
            k = n - d + 1
            for q in sorted({d + 1, d + 2, 2 * d, 3 * d,
                             n - 1, n, n * n, d * d + 2 * d - 1}):
                if q <= d:
                    continue
                a = weights(n, k, q)
                fs = failures(a)
                predicted = prediction(n, k, q)
                require(predicted == (not fs), f"Main criterion: {(n,k,q)}")
                require(sum(a) == q ** k, f"Total: {(n,k,q)}")
                require(all(a[w] > 0 for w in range(d, n + 1)), "Positivity")
                if fs:
                    require(fs[0]["weight"] == d + 1, "First failure is not first triple")
                digest.update(f"{n},{k},{q},{int(predicted)};".encode())
                counts["q_greater_than_d"] += 1

    for d in range(3, 201):
        for k in range(2, 81):
            n = d + k - 1
            a = weights(n, k, d)
            require(prediction(n,k,d) == (not failures(a)), f"Gap case: {(n,k,d)}")
            require(sum(a) == d ** k, "Gap total")
            counts["q_equals_d_ge_3"] += 1
    for n in range(2, 501):
        a = weights(n, n-1, 2)
        require(a == [comb(n,w) if w % 2 == 0 else 0 for w in range(n+1)], "Binary")
        require(not failures(a), "Binary log-concavity")
        counts["binary_boundary"] += 1
    for n in range(2, 101):
        for q in (2, 3, 4, 5, 7, 8, 9, 11):
            for k in (1, n):
                a = weights(n,k,q)
                require(not failures(a) and prediction(n,k,q), "Degenerate case")
                counts["degenerate"] += 1
            if q >= n-1:
                a = weights(n,2,q)
                require(not failures(a) and prediction(n,2,q), "Dimension two")
                counts["degenerate"] += 1

    for n in range(3, 36):
        for k in range(1, n+1):
            d = n-k+1
            for q in sorted({max(2,d), d+1, n+1}):
                a = weights(n,k,q)
                require(a == weights_inclusion_exclusion(n,k,q), "Independent formula")
                counts["independent_formula"] += 1

    # Check the central rational inequality with Fraction, not floats.
    for n in range(6, 61):
        for d in range(2, n-3):
            k = n-d+1
            for q in sorted({d+1, n-1, 2*n}):
                terms = [Fraction(1)]
                partial = [Fraction(1)]
                for s in range(1,k):
                    terms.append(terms[-1]*Fraction(d+s-2,s*(q-1)))
                    partial.append(partial[-1]+(-1)**s*terms[-1])
                def defect(s: int) -> Fraction:
                    return (terms[s]+terms[s+1])/partial[s] + terms[s]*terms[s+1]/partial[s]**2
                def curvature(s: int) -> Fraction:
                    return Fraction(n+1,(d+s)*(n-d-s))
                h1 = defect(1)/curvature(1)
                for s in range(3,k-1,2):
                    hs = defect(s)/curvature(s)
                    require(hs <= Fraction(s,2**(s-1))*h1, "Defect contraction")
                    counts["rational_defect_bound"] += 1

    actual = []
    for p in (3,5,7,11):
        for n in range(3, min(p,6)+1):
            for k in range(1,min(n,3)+1):
                a = enumerate_rs(p,n,k)
                require(a == weights(n,k,p), "RS enumeration")
                require((not failures(a)) == prediction(n,k,p), "RS criterion")
                actual.append({"family":"Reed-Solomon", "n":n,"k":k,"q":p})
                counts["actual_codewords"] += p**k
    for q,max_n in ((2,8),(3,6),(4,7),(5,6),(7,5)):
        for n in range(2,max_n+1):
            a = enumerate_parity(q,n)
            require(a == weights(n,n-1,q), "Parity enumeration")
            require((not failures(a)) == prediction(n,n-1,q), "Parity criterion")
            actual.append({"family":"single-parity-check", "n":n,"k":n-1,"q":q})
            counts["actual_codewords"] += q**(n-1)
    a = enumerate_hexacode()
    require(a == [1,0,0,0,45,0,18] == weights(6,3,4), "Hexacode")
    actual.append({"family":"hexacode", "n":6,"k":3,"q":4})
    counts["actual_codewords"] += 64
    counts["actual_code_enumerations"] = len(actual)

    examples = []
    for n,k,q in [(5,3,5),(5,3,7),(11,9,11),(4,3,3),(7,6,4),
                  (15,14,5),(16,15,5),(6,3,4),(10,7,8),(18,15,16)]:
        a = weights(n,k,q)
        d = n-k+1
        example = {"n":n,"k":k,"d":d,"q":q,"weights":a,
                   "log_concave":not failures(a),"failures":failures(a)}
        if k>=3 and q>d:
            example["twice_P"] = twice_quadratic(n,k,q)
            example["first_difference"] = a[d+1]**2-a[d]*a[d+2]
        examples.append(example)
    result = {"status":"all checks passed", "python":platform.python_version(),
              "max_n_main_sweep":args.max_n, "counts":counts,
              "main_sweep_digest_sha256":digest.hexdigest(),
              "elapsed_seconds":round(time.monotonic()-start,3),
              "formal_sweep_does_not_establish_code_existence":True,
              "actual_codes":actual,"examples":examples}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k not in ("actual_codes","examples")},indent=2))


if __name__ == "__main__":
    main()
