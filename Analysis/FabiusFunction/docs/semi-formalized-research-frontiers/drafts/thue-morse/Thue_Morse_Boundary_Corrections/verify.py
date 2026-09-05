#!/usr/bin/env python3
"""Exact checks for 'Exact Boundary Corrections for Thue--Morse Diffraction'.

Python 3.9+; standard library only. Run: python verify.py --output verification.json
All identity checks use integers or fractions.Fraction, never floating point.
The floating-point exponents in the report are descriptive, not proof evidence.
The mathematical proofs are in the accompanying article.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as F
from functools import lru_cache
from math import log2, sqrt
from pathlib import Path
from typing import Dict, List

CHECKS: Dict[str, int] = {}

def check(condition: bool, group: str, context: object = None) -> None:
    if not condition:
        raise AssertionError(f"{group}: {context}")
    CHECKS[group] = CHECKS.get(group, 0) + 1


def epsilon(n: int) -> int:
    if n < 0:
        raise ValueError("The sequence is indexed by nonnegative integers.")
    return 1 - 2 * (bin(n).count("1") % 2)


@lru_cache(maxsize=None)
def eta(k: int) -> F:
    k = abs(k)
    if k == 0:
        return F(1)
    if k == 1:
        return F(-1, 3)
    if k % 2 == 0:
        return eta(k // 2)
    return -(eta(k // 2) + eta(k // 2 + 1)) / 2


@lru_cache(maxsize=None)
def g(k: int) -> int:
    if k < 0:
        raise ValueError("g is indexed by nonnegative integers.")
    if k <= 1:
        return k
    if k % 2 == 0:
        return -2 * g(k // 2)
    return g(k // 2) + g(k // 2 + 1)


def multiply_riesz(coeff: Dict[int, F], frequency: int, a: F) -> Dict[int, F]:
    """Multiply a Laurent polynomial by 1-a(z^frequency+z^-frequency)/2."""
    out = dict(coeff)
    for k, value in coeff.items():
        for shift in (-frequency, frequency):
            out[k + shift] = out.get(k + shift, F(0)) - a * value / 2
    return {k: value for k, value in out.items() if value}


def partition_coefficients(limit: int) -> List[int]:
    """Coefficients of product_j (1-z^(2^j))^-2, via two colors per size."""
    p = [1] + [0] * limit
    size = 1
    while size <= limit:
        for _color in range(2):
            for n in range(size, limit + 1):
                p[n] += p[n - size]
        size *= 2
    return p


def main(max_level: int) -> dict:
    CHECKS.clear()
    if not 0 <= max_level <= 13:
        raise ValueError("Choose --max-level between 0 and 13 (direct tests are quadratic).")
    finite: Dict[int, Dict[int, F]] = {0: {0: F(1)}}
    for m in range(max_level + 2):
        finite[m + 1] = multiply_riesz(finite[m], 2**m, F(1))
    for m in range(max_level + 1):
        N = 2**m
        signs = [epsilon(j) for j in range(2 * N + 1)]
        for k in range(N + 1):
            direct = sum(signs[j] * signs[j + k] for j in range(N - k))
            forward = sum(signs[j] * signs[j + k] for j in range(N))
            expected = eta(k) + F((-1)**m * g(k), 3 * N)
            check(F(direct, N) == expected, "aperiodic boundary", (m, k))
            check(finite[m].get(k, F(0)) == expected, "independent Laurent product", (m, k))
            check(F(forward, N) == eta(k) - F(2 * (-1)**m * g(k), 3 * N),
                  "forward boundary", (m, k))
            corrected = (finite[m].get(k, F(0)) + 2 * finite[m+1].get(k, F(0))) / 3
            check(corrected == eta(k), "positive extrapolation", (m, k))
        first = (finite[m].get(N+1, F(0)) + 2 * finite[m+1].get(N+1, F(0))) / 3
        check(first - eta(N+1) == F((-1)**m, 3*N), "first missed mode", m)

    for k in range(1, 2**max_level + 1):
        convolution = sum(epsilon(j) * epsilon(k-1-j) for j in range(k))
        check(convolution == g(k), "Stern convolution", k)
        check(abs(g(k)) <= k, "pointwise bound", k)
        v2k = (k & -k).bit_length() - 1
        v2g = (abs(g(k)) & -abs(g(k))).bit_length() - 1
        check(v2g == v2k, "exact two-adic valuation", k)

    energy_rows = []
    last_u = last_v = last_x = last_y = None
    for m in range(max_level + 3):
        N = 2**m
        u = sum(F(g(k)**2) for k in range(1, N)) + F(g(N)**2, 2)
        v = sum(F(g(k)*g(k+1)) for k in range(N))
        x = sum(eta(k)**2 for k in range(1, N)) + F(5, 9)
        y = sum(eta(k)*eta(k+1) for k in range(N))
        if m:
            check((u, v) == (6*last_u+2*last_v, -4*last_u-4*last_v),
                  "Stern energy transfer", m)
            check((x, y) == ((6*last_x+2*last_y)/4, -last_x-last_y),
                  "correlation energy transfer", m)
        if m in finite:
            # Parseval: integral f_m^2 = sum of squares of Laurent coefficients.
            check(sum(c*c for c in finite[m].values()) == 2*u/N**2,
                  "fourth moment Parseval", m)
        energy_rows.append({"m": m, "U_m": str(u), "X_m": str(x)})
        last_u, last_v, last_x, last_y = u, v, x, y

    limit = 256
    p = partition_coefficients(limit)
    kap = [F(1)]
    for n in range(1, limit + 1):
        kap.append(F(3*p[n], 2) - (kap[n//2]/2 if n % 2 == 0 else F(0)))
        j, total, scale = n, F(0), F(1)
        while True:
            total += scale * p[j]
            if j % 2:
                break
            j //= 2
            scale /= -2
        check(kap[n] == F(3, 2) * total, "finite partition coefficient formula", n)
        check(F(3, 4)*p[n] <= kap[n] <= F(3, 2)*p[n], "K positivity bounds", n)
    for n in range(1, limit + 1):
        coeff = sum(F(g(j))*kap[n-j] for j in range(1, n+1))
        check(coeff == -3*eta(n), "K defining analytic identity", n)
    for m in range(min(max_level, 7) + 1):
        N = 2**m
        for k in range(1, limit + 1):
            rhs = F((-1)**m, 3*N) * sum(
                F(g(k-j*N))*kap[j] for j in range((k-1)//N+1))
            check(finite[m].get(k, F(0))-eta(k) == rhs,
                  "all-mode disk factorization", (m, k))

    parameters = [F(-1), F(-3, 4), F(-2, 3), F(-1, 2), F(-1, 7),
                  F(1, 7), F(1, 4), F(1, 2), F(1)]
    for a in parameters:
        @lru_cache(maxsize=None)
        def h(k: int) -> F:
            if k == 0: return F(1)
            if k == 1: return -a/(2+a)
            if k % 2 == 0: return h(k//2)
            return -a*(h(k//2)+h(k//2+1))/2
        @lru_cache(maxsize=None)
        def ga(k: int) -> F:
            if k <= 1: return F(k)
            if k % 2 == 0: return -2*ga(k//2)/a
            return ga(k//2)+ga(k//2+1)
        coeff = {0: F(1)}
        b = -2/a
        previous = None
        for m in range(8):
            N = 2**m
            next_coeff = multiply_riesz(coeff, N, a)
            for k in range(N+1):
                check(coeff.get(k, F(0))-h(k) == a/(2+a)*(-a/2)**m*ga(k),
                      "parameter boundary", (str(a), m, k))
                check((a*coeff.get(k, F(0))+2*next_coeff.get(k, F(0)))/(2+a) == h(k),
                      "parameter moment exactness", (str(a), m, k))
            u = sum(ga(k)**2 for k in range(1, N)) + ga(N)**2/2
            v = sum(ga(k)*ga(k+1) for k in range(N))
            x = sum(h(k)**2 for k in range(1, N)) + (1+h(1)**2)/2
            y = sum(h(k)*h(k+1) for k in range(N))
            if previous:
                pu, pv, px, py = previous
                check((u,v) == ((b*b+2)*pu+2*pv, 2*b*(pu+pv)),
                      "parameter Stern energy", (str(a),m))
                check((x,y) == ((1+a*a/2)*px+a*a*py/2, -a*(px+py)),
                      "parameter correlation energy", (str(a),m))
            previous = (u,v,x,y)
            coeff = next_coeff
        # Positivity is proved for all x in the article, not inferred by sampling.
        check((abs(2*a/(2+a)) <= 1) == (a >= F(-2,3)),
              "parameter positivity threshold", str(a))

    sigma = log2((1+sqrt(17))/4)/2
    return {
        "status": "PASS", "arithmetic": "exact integers and rational fractions",
        "checks_total": sum(CHECKS.values()), "checks_by_group": CHECKS,
        "direct_correlation_levels": [0,max_level],
        "parameter_values": [str(a) for a in parameters],
        "parameter_levels": [0,7], "analytic_coefficient_cutoff": limit,
        "g_0_to_16": [g(k) for k in range(17)],
        "eta_0_to_16": [str(eta(k)) for k in range(17)],
        "p2_0_to_16": p[:17], "kappa_0_to_16": [str(v) for v in kap[:17]],
        "energy_rows": energy_rows,
        "exponents_approximate": {"sigma": sigma, "s_star": 1+sigma},
        "scope": "Finite tests support the implementation; proofs and infinite-limit statements are in the article."
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    result = main(args.max_level)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {result['checks_total']:,} exact checks; report: {args.output}")
    for group, count in CHECKS.items():
        print(f"  {group}: {count}")
