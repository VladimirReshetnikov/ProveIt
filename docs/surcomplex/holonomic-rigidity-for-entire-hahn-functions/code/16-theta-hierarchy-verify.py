#!/usr/bin/env python3
"""Exact finite checks for article.tex; not a formal proof of infinite statements.

Uses only Python's standard library. Run: python3 verify.py --precision 128
The parameter means equality modulo q**precision, retaining exact polynomials in X.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import permutations, product
import json
from math import comb, factorial, isqrt
from pathlib import Path
from time import perf_counter

Poly = dict[tuple[int, int], int]  # (q exponent, X exponent) -> integer


def clean(p: Poly) -> Poly:
    return {m: a for m, a in p.items() if a}


def add(*polys: Poly) -> Poly:
    r: Poly = {}
    for p in polys:
        for m, a in p.items():
            r[m] = r.get(m, 0) + a
    return clean(r)


def scale(p: Poly, a: int) -> Poly:
    return clean({m: a*b for m, b in p.items()})


def mul(p: Poly, q: Poly, precision: int) -> Poly:
    r: Poly = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            if i+k < precision:
                m = (i+k, j+l)
                r[m] = r.get(m, 0) + a*b
    return clean(r)


def power(p: Poly, n: int, precision: int) -> Poly:
    r = {(0, 0): 1}
    for _ in range(n):
        r = mul(r, p, precision)
    return r


def dx(p: Poly) -> Poly:
    return {(i, j-1): j*a for (i, j), a in p.items() if j}


def chebyshev(nmax: int) -> list[Poly]:
    cs: list[Poly] = [{(0, 0): 2}, {(0, 1): 1}]
    for n in range(1, nmax):
        shifted = {(0, j+1): a for (_, j), a in cs[-1].items()}
        cs.append(add(shifted, scale(cs[-2], -1)))
    return cs[:nmax+1]


def s_lambert(k: int, precision: int) -> Poly:
    r: Poly = {}
    for n in range(1, (precision-1)//2+1):
        for j in range(2*n, precision, 2*n):
            r[(j, 0)] = r.get((j, 0), 0) + n**k
    return r


def q_coefficient(p: Poly, n: int) -> dict[int, int]:
    return {j: a for (i, j), a in p.items() if i == n}


def sign_qsqrt2(a: F, b: F) -> int:
    """Sign of a+b*sqrt(2), by rational comparisons only."""
    if b == 0:
        return (a > 0) - (a < 0)
    if a == 0:
        return (b > 0) - (b < 0)
    if a > 0 and b > 0:
        return 1
    if a < 0 and b < 0:
        return -1
    gap = a*a - 2*b*b
    if gap == 0:
        return 0
    return ((gap > 0) - (gap < 0)) * ((a > 0) - (a < 0))


def run(precision: int) -> dict:
    started = perf_counter()
    report: dict = {"precision_exclusive": precision, "arithmetic": "exact integers and rational numbers"}
    cs = chebyshev(max(30, isqrt(precision-1)))
    coefficient_comparisons = 0
    for n in range(1, 31):
        direct: Poly = {}
        for j in range(n//2+1):
            value = F(n, n-j)*comb(n-j, j)*(-1)**j
            assert value.denominator == 1
            direct[(0, n-2*j)] = value.numerator
        assert cs[n] == direct
        coefficient_comparisons += 1
    report["chebyshev_polynomial_comparisons"] = coefficient_comparisons

    f: Poly = {(0, 0): 1}
    for n in range(1, isqrt(precision-1)+1):
        f = add(f, {(n*n, j): a for (_, j), a in cs[n].items()})
    leading = 0
    for j in range(isqrt(precision-1)+1):
        support = [(i, a) for (i, k), a in f.items() if k == j]
        assert min(support) == (j*j, 1)
        leading += 1
    report["leading_coefficient_checks"] = leading

    prod: Poly = {(0, 0): 1}
    for n in range(1, (precision-1)//2+1):
        prod = mul(prod, {(0, 0): 1, (2*n, 0): -1}, precision)
    for j in range(1, precision, 2):
        factor = {(0, 0): 1, (j, 1): 1}
        if 2*j < precision:
            factor[(2*j, 0)] = 1
        prod = mul(prod, factor, precision)
    for n in range(precision):
        assert q_coefficient(prod, n) == q_coefficient(f, n), ("Jacobi product", n)
    report["jacobi_product_q_coefficient_comparisons"] = precision

    delta: Poly = {(0, 2): 1, (0, 0): -4}
    xp: Poly = {(0, 1): 1}
    s1, s3, s5 = [s_lambert(k, precision) for k in (1, 3, 5)]
    a4 = scale(s3, -5)
    a6num = add(scale(s3, -5), scale(s5, -7))
    assert all(a % 12 == 0 for a in a6num.values())
    a6 = {m: a//12 for m, a in a6num.items()}
    fp, fpp = dx(f), dx(dx(f))
    f2 = power(f, 2, precision)
    B = add(mul(delta, add(mul(f, fpp, precision), scale(mul(fp, fp, precision), -1)), precision),
            mul(xp, mul(f, fp, precision), precision))
    A = add(scale(B, -1), scale(mul(s1, f2, precision), -2))
    C = add(mul(f, dx(A), precision), scale(mul(fp, A, precision), -2))
    lhs = mul(delta, power(C, 2, precision), precision)
    rhs = add(scale(power(A, 3, precision), 4),
              mul(power(A, 2, precision), f2, precision),
              scale(mul(a4, mul(A, power(f, 4, precision), precision), precision), 4),
              scale(mul(a6, power(f, 6, precision), precision), 4))
    for n in range(precision):
        assert q_coefficient(lhs, n) == q_coefficient(rhs, n), ("order-three identity", n)
    report["differential_identity_q_coefficient_comparisons"] = precision

    gauss_checks = 0
    for h in [F(1, 5), F(1, 2), F(1), F(3, 2), F(2), F(5, 2)]:
        for r in [F(-5, 3)] + [F(k, 7) for k in range(141)]:
            center = r/(2*h)
            bound = max(5, int(center)+5)
            brute = min(h*n*n-r*n for n in range(bound+1))
            if r < 0:
                predicted = F(0)
            else:
                lo = center.numerator//center.denominator
                dist = min(abs(center-lo), abs(center-(lo+1)))
                predicted = -r*r/(4*h)+h*dist*dist
                assert 0 <= predicted+r*r/(4*h) <= h/4
            assert brute == predicted
            gauss_checks += 1
    report["exact_gauss_profile_cases"] = gauss_checks

    threshold_cases = 0
    # The two-scale example: h1=1, h2=1/sqrt(2). Compare actual discrete minima exactly.
    for r in range(16, 81):
        w1 = min(F(n*n-r*n) for n in range(2*r+1))
        w2 = (F(0), F(0))
        for n in range(2*r+1):
            candidate = (F(-r*n), F(n*n, 2))
            if sign_qsqrt2(candidate[0]-w2[0], candidate[1]-w2[1]) < 0:
                w2 = candidate
        # w(F1**2)=2w1; w((X+t^-7)F2)=min(-r,-7)+w2.
        assert sign_qsqrt2(w2[0]+min(-r, -7)-2*w1, w2[1]) > 0
        assert 0 > 2*w1
        threshold_cases += 1
    report["irrational_scale_dominance_cases"] = threshold_cases

    assignments = {}
    for n in range(1, 9):
        admissible = [p for p in permutations(range(n)) if all(p[j] <= j for j in range(n))]
        assert admissible == [tuple(range(n))]
        assignments[str(n)] = len(admissible)
    report["squarefree_wedge_assignment_counts"] = assignments

    nonzero = 0
    for c00, c01, c10, c11 in product(range(3), repeat=4):
        det = c00*c11-c01*c10
        nonzero += bool(det)
    assert nonzero > 0
    report["constant_independent_pair_grid"] = {"candidates": 81, "nonzero_jet_determinants": nonzero}
    report["status"] = "PASS"
    report["elapsed_seconds"] = round(perf_counter()-started, 3)
    report["not_proved_by_tests"] = [
        "strong summability for arbitrary Hahn supports",
        "algebraic independence of full infinite functions",
        "existence of a successful compression candidate for every field extension",
        "minimal differential orders or continuum cardinality",
        "independent refereeing or Lean formal verification"
    ]
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    if not 16 <= args.precision <= 512:
        parser.error("precision must lie between 16 and 512")
    report = run(args.precision)
    text = json.dumps(report, indent=2)
    args.output.write_text(text+"\n", encoding="utf-8")
    print(text)

if __name__ == "__main__":
    main()
