#!/usr/bin/env python3
"""Reproduce exact finite audits. Standard library only; Python >= 3.10.

Usage: python code/verify.py [--scan 200] [--bm-max 30]
Outputs are written to data/. Failure raises an exception, including under -O.
No exhaustive search for the true DFAO optimum is performed by this program.
"""
from __future__ import annotations

import argparse
import itertools
import json
import platform
from math import factorial, prod
from pathlib import Path

from spectral import (full_factors, moments, multiply, polynomial,
                      positive_coloring, residue_factors, signed_coloring,
                      tail_numerator, witness_values)

ROOT = Path(__file__).resolve().parents[1]


def check(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def berlekamp_massey(sequence: list[int], prime: int) -> list[int]:
    """Minimal finite-sequence connection polynomial, constant term one."""
    C, B, L, m, b = [1], [1], 0, 1, 1
    for n in range(len(sequence)):
        discrepancy = sum(C[j] * sequence[n-j] for j in range(len(C)) if j <= n) % prime
        if discrepancy == 0:
            m += 1
            continue
        old = C[:]
        scale = discrepancy * pow(b, -1, prime) % prime
        needed = len(B) + m
        C.extend([0] * max(0, needed - len(C)))
        for j in range(len(B)):
            C[j+m] = (C[j+m] - scale * B[j]) % prime
        if 2 * L <= n:
            L, B, b, m = n + 1 - L, old, discrepancy, 1
        else:
            m += 1
    C.extend([0] * max(0, L + 1 - len(C)))
    return C[:L+1]


def falling(x: int, d: int) -> int:
    return prod(x - j for j in range(d))


def P12(x: int, j: int) -> int:
    return ((1+12**j)*falling(x, 6)
            - factorial(12)//(factorial(2)*factorial(6))*(2**j+6**j)*x
            + factorial(12)//(factorial(3)*factorial(4))*(3**j+4**j))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan", type=int, default=200)
    parser.add_argument("--bm-max", type=int, default=30)
    args = parser.parse_args()
    check(args.scan >= 19 and args.bm_max >= 19, "limits must both be >= 19")
    out = ROOT / "data"
    out.mkdir(exist_ok=True)
    summary: dict = {"python": platform.python_version(), "scan_max_k": args.scan,
                     "bm_max_k": args.bm_max,
                     "sequence": "D*_k only; optimum transfer is not tested"}

    # Independent literal colorings, positive Stirling and signed multinomials.
    brute_cases = 0
    for k in range(3, 6):
        for a in range(1, 4):
            for b in range(1, 4):
                brute = sum(set(c[:a]).isdisjoint(c[a:])
                            for c in itertools.product(range(k), repeat=a+b))
                check(brute == positive_coloring(k,a,b) == signed_coloring(k,a,b),
                      f"literal coloring disagreement at {(k,a,b)}")
                brute_cases += 1
    formula_cases = 0
    for k in range(3, 16):
        for a in range(1, 10):
            for b in range(1, 10):
                check(positive_coloring(k,a,b) == signed_coloring(k,a,b),
                      f"coloring formula disagreement at {(k,a,b)}")
                formula_cases += 1
    summary["literal_coloring_cases"] = brute_cases
    summary["signed_positive_cases"] = formula_cases

    # Three-moment scans and Fourier support: exact integers, not floating point.
    cancelled, full_cancelled, table_rows, spectra = [], [], [], []
    for k in range(3, args.scan + 1):
        data = moments(k)
        for p, m in data.items():
            if p > 1:
                zeros = [j for j, v in zip((1,2,4), (m.T,m.U,m.V)) if v == 0]
                if zeros:
                    cancelled.append({"k":k,"p":p,"zero_moments":zeros})
                degree = sum(len(f)-1 for f in m.factors())
                if m.off_diagonal and degree < 4:
                    full_cancelled.append({"k":k,"p":p,"degree":degree})
                if p % 4 != 0:
                    check(not zeros, "parity noncancellation failed")
                    check(degree == (4 if m.off_diagonal else 1),
                          "parity Fourier support failed")
        if k <= args.bm_max:
            factors = full_factors(k,data)
            residues = [sum(len(f)-1 for f in residue_factors(k,r,data)) for r in range(4)]
            row = {"k":k,"products":len(data),"residue_orders":residues,
                   "full_order":sum(len(f)-1 for f in factors)}
            table_rows.append(row)
            spectra.append({**row,"full_factors_ascending":factors,
                            "moments":[{"p":p,"T":m.T,"U":m.U,"V":m.V}
                                       for p,m in data.items()]})
    check({"k":19,"p":12,"zero_moments":[1]} in cancelled, "missing k=19 exception")
    summary["cancelled_residue_moments"] = cancelled
    summary["off_diagonal_full_cancellations"] = full_cancelled

    # Recover full and residue recurrences from a different counting formula.
    bm_checks = 0
    primes = [1_000_000_007, 998_244_353]
    for k in range(3,args.bm_max+1):
        data = moments(k)
        q = polynomial(full_factors(k,data))
        d = len(q)-1
        start = max(7,k+1)
        for prime in primes:
            values = witness_values(k,list(range(start,start+2*d+16)),prime)
            actual = berlekamp_massey(values,prime)
            expected = [c % prime for c in q[::-1]]
            check(actual == expected, f"full modular recurrence mismatch k={k}, mod={prime}")
            bm_checks += 1
            for r in range(4):
                qr = polynomial(residue_factors(k,r,data))
                dr = len(qr)-1
                t0 = max(0,(start-r+3)//4)
                indices = [4*(t0+i)+r for i in range(2*dr+16)]
                values = witness_values(k,indices,prime)
                check(berlekamp_massey(values,prime) == [c%prime for c in qr[::-1]],
                      f"residue recurrence mismatch k={k}, r={r}, mod={prime}")
                bm_checks += 1
    summary["modular_recurrence_checks"] = bm_checks
    summary["moduli"] = primes

    # Direct rational-integer numerator checks, including many subsequent zeros.
    gf_data, gf_checks = [], 0
    for k in range(3,11):
        numerator, denominator = tail_numerator(k,7)
        d = len(denominator)-1
        values = witness_values(k,list(range(7,7+d+20)))
        convoluted = [sum(denominator[j]*values[i-j]
                          for j in range(min(i,d)+1)) for i in range(len(values))]
        check(all(x == 0 for x in convoluted[d:]), f"GF denominator failed k={k}")
        check(convoluted[:len(numerator)] == numerator, f"GF numerator failed k={k}")
        gf_data.append({"k":k,"start":7,"numerator_ascending":numerator,
                        "denominator_ascending":denominator})
        gf_checks += 1
    summary["exact_tail_generating_function_checks"] = gf_checks

    # Product-12 polynomial identity and exact finite part of its sign proof.
    for k in range(7,101):
        m = moments(k)[12]
        for j, actual in zip((1,2,4),(m.T,m.U,m.V)):
            check(actual*factorial(12) == (-1)**(k-7)*falling(k,7)*P12(k-7,j),
                  f"product12 polynomial mismatch k={k}, j={j}")
    minimum_locations = {1:11,2:10,4:8}
    p12_rows = []
    for x in range(14):
        p12_rows.append({"x":x,"P1":P12(x,1),"P2":P12(x,2),"P4":P12(x,4),
                         "R":P12(x,4)-12*P12(x,2)})
    for j, h in minimum_locations.items():
        A = 1 + 12**j
        B = factorial(12)//(factorial(2)*factorial(6))*(2**j+6**j)
        check(6*A*falling(h-1,5)-B < 0 < 6*A*falling(h,5)-B,
              f"wrong difference crossing j={j}")
        check(P12(13,j)>0, f"wrong final positivity j={j}")
        check([x for x in range(14) if P12(x,j)==0] == ([12] if j==1 else []),
              f"wrong finite root list j={j}")
    check(6*18997*falling(6,5)-276756480 < 0 < 6*18997*falling(7,5)-276756480,
          "wrong difference crossing for R")
    R = lambda x: P12(x,4)-12*P12(x,2)
    check([R(x) for x in (0,1,9,10)] == [123076800,-153679680,-1218792960,227858400],
          "wrong full product12 support certificate")
    summary["product12_R_integer_roots_x_nonnegative"] = []
    summary["product12_polynomial_identity_cases"] = 94*3
    summary["product12_integer_roots_x_nonnegative"] = {"P1":[12],"P2":[],"P4":[]}

    m = moments(19)[12]
    summary["nineteen_output_certificate"] = {"T":m.T,"U":m.U,"V":m.V,
                                               "pairs":m.pairs,"W":m.W,"Z":m.Z}
    for name, value in [("audit.json",summary),("spectra.json",spectra),
                        ("tail_generating_functions.json",gf_data),
                        ("product12_polynomials.json",p12_rows)]:
        (out/name).write_text(json.dumps(value,indent=2)+"\n",encoding="utf-8")
    lines = []
    for row in table_rows:
        if row["k"] <= 20 or row["k"] in (25,30):
            a,b,c,d = row["residue_orders"]
            lines.append(f'{row["k"]} & {row["products"]} & {a} & {b} & {c} & {d} & {row["full_order"]} \\\\')
    (out/"orders.tex").write_text("\n".join(lines)+"\n",encoding="utf-8")
    print(json.dumps(summary,indent=2))


if __name__ == "__main__":
    main()
