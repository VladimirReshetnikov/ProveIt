#!/usr/bin/env python3
"""Independent exact audit of the (2,2b) late-coordinate matrix.

This verifier reconstructs each coordinate directly from the finite
summation-by-parts identity and uncentered Hurwitz-tail coefficients.
The proposed matrix formula enters only the final comparison.  No project
files or other verification scripts are imported.

Dependency: sympy==1.14.0.  Run with Python 3.10 or later.
"""
from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path

import sympy as sp

N = sp.Symbol("N")
EULER = sp.Symbol("EulerGamma")
HERE = Path(__file__).resolve().parent


@lru_cache(None)
def tail_coefficient(p: int, exponent: int):
    """Coefficient of N^-exponent in zeta(p,N+1), with p>=2."""
    if exponent == p - 1:
        return sp.Rational(1, p - 1)
    if exponent == p:
        return -sp.Rational(1, 2)
    difference = exponent - p + 1
    if difference >= 2 and difference % 2 == 0:
        k = difference // 2
        return sp.bernoulli(2*k, 0)*sp.rf(p, 2*k - 1)/sp.factorial(2*k)
    return sp.S.Zero


@lru_cache(None)
def power_sum(m: int):
    """The polynomial sum_{k=1}^N k^m, including the m=0 case."""
    expression = (sp.bernoulli(m+1, N+1)-sp.bernoulli(m+1, 1))/(m+1)
    return sp.Poly(sp.expand(expression), N)


def scalar_sum_constant(exponent: int):
    """Constant term of sum_{k=1}^N k^exponent."""
    if exponent >= 0:
        return sp.S.Zero
    if exponent == -1:
        return EULER
    return sp.Symbol(f"Z{-exponent}")


@lru_cache(None)
def linear_tail_constant(m: int, p: int):
    """Constant term of sum k^m*zeta(p,k+1), from its finite identity."""
    F = power_sum(m)
    # Boundary term F(N)*zeta(p,N+1).
    result = sum(coefficient*tail_coefficient(p, exponent)
                 for (exponent,), coefficient in F.terms())
    # Exact remaining sum F(k-1)/k^p.
    shifted = sp.Poly(F.as_expr().subs(N, N-1), N)
    for (exponent,), coefficient in shifted.terms():
        result += coefficient*scalar_sum_constant(exponent-p)
    return sp.expand(result)


def cutoff_coordinate(b: int, j: int):
    """CT of E_{2j+1}(N), without using the claimed Bernoulli matrix."""
    q = 2*b
    d = 2*j+1
    # Boundary N^d*A_2(N)*A_q(N).
    result = sum(tail_coefficient(2, a)*tail_coefficient(q, d-a)
                 for a in range(1, d))
    result += linear_tail_constant(d-q, 2)
    result += linear_tail_constant(d-2, q)
    result += scalar_sum_constant(d-q-2)
    return sp.expand(result)


def proposed_coordinate(b: int, row: int):
    """Independent comparison target: the printed late-block formula."""
    result = sp.S.Zero
    for k in range(b):
        mu = sp.bernoulli(2*(row+k), 0)/sp.factorial(2*(row+k))
        entry = sp.factorial(2*b+2*row-1)*mu/sp.factorial(2*b-2*k)
        if k == 0:
            entry += sp.Rational(2*row+1, 2)*sp.bernoulli(2*row, 0)
            result -= entry/2  # zeta(0)=-1/2
        else:
            result += entry*sp.Symbol(f"Z{2*k}")
    return sp.expand(result)


def main():
    # Guards against the m=0 Faulhaber convention mistake found in the audit.
    assert power_sum(0).as_expr() == N
    for m in range(8):
        for cutoff in (0, 1, 3, 7):
            assert power_sum(m).eval(cutoff) == sum(k**m for k in range(1, cutoff+1))
    report = {
        "status": "passed",
        "arithmetic": "exact rational arithmetic with formal zeta and EulerGamma symbols",
        "method": "finite summation by parts, Faulhaber polynomials, uncentered Hurwitz-tail coefficient extraction",
        "dependency": {"sympy": sp.__version__},
        "range": {"b_min": 2, "b_max": 8, "j": "b through 2b-1"},
        "row_count": 0,
        "faulhaber_checks": 32,
        "blocks": [],
    }
    for b in range(2, 9):
        for row in range(b):
            value = cutoff_coordinate(b, b+row)
            assert not value.has(EULER), (b, row, "uncancelled EulerGamma", value)
            difference = sp.expand(value-proposed_coordinate(b, row))
            assert difference == 0, (b, row, difference)
            report["row_count"] += 1
        report["blocks"].append({"b": b, "rows_checked": b,
                                  "all_differences": "0", "EulerGamma_cancels": True})
    assert report["row_count"] == 35
    (HERE/"reconstruction_cutoff_audit.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
