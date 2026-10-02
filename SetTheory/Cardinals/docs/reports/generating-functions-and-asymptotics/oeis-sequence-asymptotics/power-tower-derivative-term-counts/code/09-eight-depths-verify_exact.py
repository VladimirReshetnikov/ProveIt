#!/usr/bin/env python3
"""Exact arithmetic checks for the A290268 eight-depth article.

Uses only Python's standard library. No floating point is used in a test.
This checks rational anchors and finite cross-checks, not the analytic proofs.
Run from the package directory:
    python3 code/verify_exact.py > data/exact_results.json
"""
from __future__ import annotations
import json
import sys
from fractions import Fraction
from math import comb, factorial
from typing import Iterable

SETTINGS = [
    (3, Fraction(10, 3), 14, 39, (3517, 3408, 3627)),
    (4, Fraction(10), 89, 192, (10119, 10033, 10101)),
    (5, Fraction(19), 398, 814, (19037, 19002, 19024)),
    (6, Fraction(30), 1461, 2944, (30014, 30002, 30010)),
    (7, Fraction(43), 5078, 10183, (43006, 43003, 43005)),
    (8, Fraction(58), 16613, 33257, (58003, 58002, 58003)),
]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def linear(a: list[int], constant: int, slope: int = 1) -> list[int]:
    """Multiply by constant + slope*u, truncated to the input length."""
    return [constant*x + (slope*a[i-1] if i else 0) for i, x in enumerate(a)]


def falling_jet(p: int, length: int, degree: int) -> list[int]:
    a = [1] + [0]*degree
    for i in range(length):
        a = linear(a, p-i)
    return a


def jets(d: int, q: int, max_k: int, degree: int) -> Iterable[list[int]]:
    p = 2*d
    r = p+q+1
    current = falling_jet(p, r, degree)
    previous = [0]*(degree+1)
    for k in range(max_k+1):
        yield current
        nxt = linear(current, p-q, 2)
        nxt = [a+k*(k+r)*b for a, b in zip(nxt, previous)]
        previous, current = current, nxt


def fraction_string(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def arctan_interval(inverse: int, pairs: int) -> tuple[Fraction, Fraction]:
    """Alternating-series lower (2*pairs terms) and upper (+1 term)."""
    lower = sum((Fraction((-1)**i, (2*i+1)*inverse**(2*i+1))
                 for i in range(2*pairs)), Fraction())
    upper = lower + Fraction(1, (4*pairs+1)*inverse**(4*pairs+1))
    return lower, upper


def pi_certificate() -> dict:
    a_lo, a_hi = arctan_interval(5, 3)
    b_lo, b_hi = arctan_interval(239, 2)
    lo, hi = 16*a_lo-4*b_hi, 16*a_hi-4*b_lo
    require(lo > 0 and lo*lo > Fraction(49, 5), "pi lower interval failed")
    require(hi*hi < 10, "pi upper interval failed")
    coarse_lo = 16*(Fraction(1,5)-Fraction(1,375))-Fraction(4,239)
    coarse_hi = 16*(Fraction(1,5)-Fraction(1,375)+Fraction(1,15625)) - 4*(Fraction(1,239)-Fraction(1,3*239**3))
    require(coarse_lo > Fraction(157,50), "appendix lower bound")
    require(coarse_hi < Fraction(22,7), "appendix upper bound")
    return {"method": "Machin identity and alternating rational arctangent bounds",
            "appendix_coarse_interval_checked": ["157/50", "22/7"],
            "pi_lower": fraction_string(lo), "pi_upper": fraction_string(hi),
            "pi_squared_lower": "49/5", "pi_squared_upper": "10/1",
            "passed": True}


def mean_lower_pair(a: list[int], d: int) -> tuple[int, int]:
    # Rational L is strictly below the mean because pi^2 > 49/5.
    if d % 2:
        numerator, denominator = 30*a[3]+49*a[1], 15*a[1]
    else:
        numerator, denominator = 30*a[4]+49*a[2], 5*a[2]
    require(denominator != 0, "vanishing moment denominator")
    if denominator < 0:
        numerator, denominator = -numerator, -denominator
    return numerator, denominator


def check_anchor(a: list[int], d: int, threshold: Fraction,
                 lower_milli: int, label: str) -> dict:
    num, den = mean_lower_pair(a, d)
    require(num*threshold.denominator > threshold.numerator*den,
            f"mean criterion failed: {d}, {label}")
    require(1000*num > lower_milli*den, f"printed lower bound failed: {d}, {label}")
    require(1000*num < (lower_milli+1)*den, f"printed bracket failed: {d}, {label}")
    return {"anchor": label, "strict_mean_lower_bound": f"{lower_milli}/1000",
            "rational_L_upper_bound": f"{lower_milli+1}/1000",
            "threshold": fraction_string(threshold),
            "denominator_bit_length_before_reduction": den.bit_length(), "passed": True}


def anchor_certificates() -> list[dict]:
    results = []
    for d, threshold, R, Q, lower in SETTINGS:
        require(R >= 2 and R % 2 == (d-1) % 2 and Q > 2*d,
                "invalid anchor parameters")
        if d >= 5:
            root_bound = (Fraction(d)-Fraction(49, 15*d))**2
            require(root_bound < threshold, f"cotangent bound failed at {d}")
        else:
            root_bound = threshold  # beta_3 < 10/3; beta_4 < 10.
        base = None
        for base in jets(d, 2*d, R, 4):
            pass
        require(base is not None, "missing base")
        tail0 = falling_jet(2*d, 2*d+Q+1, 4)
        tail1 = linear(tail0, 2*d-Q, 2)
        records = [check_anchor(base, d, threshold, lower[0], f"base k={R},q={2*d}"),
                   check_anchor(tail0, d, threshold, lower[1], f"tail k=0,q={Q}"),
                   check_anchor(tail1, d, threshold, lower[2], f"tail k=1,q={Q}")]
        results.append({"depth": d, "R": R, "Q": Q,
                        "largest_root_strict_upper_bound": fraction_string(root_bound),
                        "anchors": records})
        print(f"Exact mean anchors passed for depth {d}.", file=sys.stderr)
    return results


def independent_polynomial_checks() -> int:
    # Direct finite sum for M! [w^M] (2+w)^k (1+w)^(p+u),
    # independent of the centered three-term recurrence.
    checked = 0
    for d in range(1, 9):
        p = 2*d
        for q in range(13):
            for k, a in enumerate(jets(d, q, 8, d)):
                M = k+p+q+1
                total = [0]*(d+1)
                for ell in range(k+1):
                    factor = comb(k, ell)*2**(k-ell)*factorial(M)//factorial(M-ell)
                    b = falling_jet(p, M-ell, d)
                    total = [x+factor*y for x, y in zip(total, b)]
                require(total == a, f"polynomial identity failed: {d},{k},{q}")
                checked += 1
    return checked


def upper_count(N: int) -> int:
    r = N//2
    return 2*r*r+2*r+1 if N % 2 == 0 else 2*(r+1)**2-(r+1)//4


def lower_count(N: int, D: int = 8) -> int:
    if N % 2 == 0:
        bulk = (3*N*N+10*N+8)//8
    else:
        bulk = (3*N*N+12*N+1)//8
    r = N//2
    extra = sum(max(r-d, 0) for d in range(1, D+1))
    holes = sum(d % 2 == r % 2 for d in range(1, min(D, r//2)+1)) if N % 2 else 0
    return bulk+extra-holes


def differentiation_checks(max_N: int = 80) -> dict:
    H: dict[tuple[int, int, int], int] = {}
    for d in range(1, 9):
        for q in range(max_N+1):
            max_k = (max_N-2*d-1-q)//2
            if max_k >= 0:
                for k, a in enumerate(jets(d, q, max_k, d)):
                    H[d, k, q] = a[d]
    # This list is transcribed from OEIS A290268, accessed 2026-10-01.
    oeis = [1,2,5,8,13,18,25,31,41,49,61,71,85,97,113,126,145,160,181,198,
            221,240,265,285,313,335,365,389,421,447,481,508,545,574,613,644,
            685,718,761,795,841,877,925,963,1013,1053,1105,1146,1201,1244,
            1301,1346,1405,1452]
    current = {(0, 0): 1}
    counts = []
    cells = 0
    for N in range(max_N+1):
        actual = len(current)
        counts.append(actual)
        if N < len(oeis):
            require(actual == oeis[N], f"OEIS term mismatch: N={N}")
        require(lower_count(N) <= actual <= upper_count(N), f"count bounds failed: N={N}")
        if N % 2 == 0 and N >= 16:
            require(lower_count(N) == (3*N*N+42*N-280)//8, "even lower polynomial")
        if N % 2 and N >= 33:
            require(lower_count(N) == (3*N*N+44*N-351)//8, "odd lower polynomial")
        for d in range(1, 9):
            for k in range((N-2*d-1)//2+1):
                q = N-2*k-2*d-1
                if q < 0:
                    continue
                value = H[d, k, q]
                require(current.get((-q-1, k), 0) == comb(N, k)*value,
                        f"coefficient bridge failed: N={N},d={d},k={k}")
                require((value == 0) == (q == 2*d and (k+d) % 2 == 0),
                        f"unexpected finite zero: N={N},d={d},k={k}")
                cells += 1
        nxt: dict[tuple[int, int], int] = {}
        for (j, k), v in current.items():
            for target, weight in [((j+1, k+1), 2), ((j+1, k), 1),
                                   ((j-1, k), j), ((j-1, k-1), k)]:
                if weight:
                    nxt[target] = nxt.get(target, 0)+weight*v
        current = {key: v for key, v in nxt.items() if v}
    return {"max_derivative_order": max_N, "bridge_cells": cells,
            "OEIS_terms_checked": len(oeis), "term_counts": counts,
            "bounds_and_bridge_passed": True}


def universal_constants() -> list[dict]:
    """Construct the all-depth bounds by integer arithmetic only."""
    rows = []
    for d in range(3, 13):
        exponent = d*(d+2)
        numerator, denominator = (d+1)**exponent, d**exponent
        B = (numerator+denominator-1)//denominator
        b = B+1
        K = b*(2*d*d+15*d+8)
        Q = 2*d+2*b*(2*d*d+15*d+11)
        T = 2*K+Q+2*d
        require(T == 2*b*(4*d*d+30*d+19)+4*d, "tail threshold identity")
        rows.append({"depth": d, "b": b, "K": K, "Q": Q, "T": T})
    return rows


def main() -> None:
    result = {"pi_certificate": pi_certificate(), "mean_anchor_certificates": anchor_certificates(),
              "independent_polynomial_identities_checked": independent_polynomial_checks(),
              "direct_differentiation": differentiation_checks(),
              "universal_bounds": universal_constants(),
              "all_checks_passed": True,
              "scope": "Exact rational anchors and finite cross-checks. Analytic proofs are in article.tex."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
