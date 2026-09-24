#!/usr/bin/env python3
"""Exact finite checks for Recovering Surreal Coefficients from Monomial Extensions.

Python 3.9+, standard library only. These checks are not a proof of the
arbitrary-rank, class-sized, or historical-novelty assertions in the article.
Run: python verify.py [--output verification.json]
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
import random
import sys
import time
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

Exp = Tuple[int, ...]
Poly = Dict[Exp, F]
COUNTS: Counter = Counter()
RNG = random.Random(20260923)


def check(condition: bool, category: str, message: str) -> None:
    if not condition:
        raise AssertionError(category + ": " + message)
    COUNTS[category] += 1


def clean(p: Poly) -> Poly:
    return {e: F(c) for e, c in p.items() if c}


def add(p: Poly, q: Poly) -> Poly:
    result = dict(p)
    for e, c in q.items():
        result[e] = result.get(e, F(0)) + c
    return clean(result)


def scale(p: Poly, c: F) -> Poly:
    return clean({e: c * a for e, a in p.items()})


def mul(p: Poly, q: Poly, cutoff: Optional[int] = None) -> Poly:
    result: Poly = {}
    for e, a in p.items():
        for f, b in q.items():
            g = tuple(x + y for x, y in zip(e, f))
            if cutoff is not None and g[0] > cutoff:
                continue
            result[g] = result.get(g, F(0)) + a * b
    return clean(result)


def power(p: Poly, n: int, cutoff: Optional[int] = None) -> Poly:
    if n < 0 or not p:
        raise ValueError("power requires a nonzero polynomial and n >= 0")
    out: Poly = {(0,) * len(next(iter(p))): F(1)}
    # Repeated multiplication keeps sparse test sizes modest.
    for _ in range(n):
        out = mul(out, p, cutoff)
    return out


def random_poly(dim: int, terms: int, radius: int = 2) -> Poly:
    exps = list(itertools.product(range(-radius, radius + 1), repeat=dim))
    chosen = RNG.sample(exps, terms)
    return {e: F(RNG.choice([-3, -2, -1, 1, 2, 3])) for e in chosen}


def is_monomial_ratio(p: Poly, q: Poly) -> bool:
    if not p or not q or len(p) != len(q):
        return False
    e, f = min(p), min(q)
    shift = tuple(a - b for a, b in zip(e, f))
    scalar = p[e] / q[f]
    shifted = {tuple(a + b for a, b in zip(g, shift)): scalar * c
               for g, c in q.items()}
    return p == shifted


def separating_functional(points: Iterable[Exp]) -> Exp:
    pts = sorted(set(points))
    if not pts:
        raise ValueError("need at least one exponent")
    d = len(pts[0])
    for base in range(2, 10000):
        ell = tuple(base ** j for j in range(d))
        images = {sum(a * b for a, b in zip(e, ell)) for e in pts}
        if len(images) == len(pts):
            return ell
    raise RuntimeError("unexpected failure to find a separating functional")


def specialize(p: Poly, ell: Exp) -> Poly:
    result: Poly = {}
    for e, c in p.items():
        key = (sum(a * b for a, b in zip(e, ell)),)
        result[key] = result.get(key, F(0)) + c
    return clean(result)


def determinant(matrix: List[List[F]]) -> F:
    a = [list(map(F, row)) for row in matrix]
    det = F(1)
    for col in range(len(a)):
        pivot = next((i for i in range(col, len(a)) if a[i][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            a[pivot], a[col] = a[col], a[pivot]
            det = -det
        v = a[col][col]
        det *= v
        for j in range(col, len(a)):
            a[col][j] /= v
        for i in range(col + 1, len(a)):
            factor = a[i][col]
            for j in range(col, len(a)):
                a[i][j] -= factor * a[col][j]
    return det


def degree(p: Poly) -> int:
    return max((e[0] for e in p), default=-1)


def divmod_poly(p: Poly, q: Poly) -> Tuple[Poly, Poly]:
    if not q:
        raise ZeroDivisionError("polynomial division by zero")
    out: Poly = {}
    rem = dict(p)
    dq = degree(q)
    while rem and degree(rem) >= dq:
        dr = degree(rem)
        term = {(dr - dq,): rem[(dr,)] / q[(dq,)]}
        out = add(out, term)
        rem = add(rem, scale(mul(term, q), F(-1)))
    return out, rem


def gcd_poly(p: Poly, q: Poly) -> Poly:
    a, b = p, q
    while b:
        _, r = divmod_poly(a, b)
        a, b = b, r
    return scale(a, 1 / a[(degree(a),)]) if a else {}


def derivative(p: Poly) -> Poly:
    return clean({(e[0] - 1,): c * e[0] for e, c in p.items() if e[0]})


def radical_degree(p: Poly) -> int:
    return degree(p) - degree(gcd_poly(p, derivative(p)))


def nonnegative_poly(d: int) -> Poly:
    result = {(j,): F(RNG.randint(-3, 3)) for j in range(d + 1)}
    result[(d,)] = F(RNG.choice([-3, -2, -1, 1, 2, 3]))
    return clean(result)


def square_root_poly(p: Poly) -> Optional[Poly]:
    """An exact rational polynomial square-root test, not a numerical test."""
    if not p:
        return {}
    n = degree(p)
    if n % 2:
        return None
    lead = p[(n,)]
    if lead < 0:
        return None
    a, b = math.isqrt(lead.numerator), math.isqrt(lead.denominator)
    if a * a != lead.numerator or b * b != lead.denominator:
        return None
    d = n // 2
    root: Poly = {(d,): F(a, b)}
    for j in range(1, d + 1):
        target = 2 * d - j
        known = mul(root, root).get((target,), F(0))
        root[(d - j,)] = (p.get((target,), F(0)) - known) / (2 * root[(d,)])
    root = clean(root)
    return root if mul(root, root) == p else None


def matvec(a: Tuple[Exp, Exp], v: Exp) -> Exp:
    return tuple(sum(x * y for x, y in zip(row, v)) for row in a)


def matmul(a: Tuple[Exp, Exp], b: Tuple[Exp, Exp]) -> Tuple[Exp, Exp]:
    return tuple(tuple(sum(a[i][l] * b[l][j] for l in range(2))
                       for j in range(2)) for i in range(2))  # type: ignore


def inverse_matrix(a: Tuple[Exp, Exp]) -> Tuple[Exp, Exp]:
    det = a[0][0] * a[1][1] - a[0][1] * a[1][0]
    if det not in (-1, 1):
        raise ValueError("test matrix is not unimodular")
    return ((a[1][1] // det, -a[0][1] // det),
            (-a[1][0] // det, a[0][0] // det))


def character(bases: Tuple[F, F], e: Exp) -> F:
    return bases[0] ** e[0] * bases[1] ** e[1]


def transform(p: Poly, matrix: Tuple[Exp, Exp], bases: Tuple[F, F]) -> Poly:
    return {matvec(matrix, e): c * character(bases, e) for e, c in p.items()}


def run_checks() -> None:
    # Classical sparse multiplicity engine: determinant identities.
    for _ in range(120):
        exps = RNG.sample(range(-25, 26), RNG.randint(1, 6))
        matrix = [[F(m ** j) for m in exps] for j in range(len(exps))]
        expected = math.prod(exps[j] - exps[i]
                             for i in range(len(exps)) for j in range(i + 1, len(exps)))
        check(determinant(matrix) == expected != 0, "vandermonde", str(exps))

    for _ in range(120):
        p = random_poly(2, RNG.randint(2, 5))
        n = RNG.randint(2, 7)
        pn = power(p, n)
        check(len(pn) >= n + 1, "sparse_polynomial_powers", "weight bound")
        ell = separating_functional(set(p) | set(pn))
        check(specialize(pn, ell) == power(specialize(p, ell), n),
              "specialization_multiplicativity", "powers commute")

    for _ in range(100):
        p, q = random_poly(2, RNG.randint(1, 4)), random_poly(2, RNG.randint(1, 4))
        if is_monomial_ratio(p, q):
            p = add(p, {(7, 0): F(1)})
        differences = {tuple(a - b for a, b in zip(e, f)) for e in p for f in q}
        ell = separating_functional(differences)
        p0, q0 = specialize(p, ell), specialize(q, ell)
        check(len(p0) == len(p) and len(q0) == len(q),
              "support_difference_separation", "individual weights")
        check(not is_monomial_ratio(p0, q0),
              "support_difference_separation", "nonmonomial ratio survives")
        n = RNG.randint(2, 6)
        pn, qn = power(p, n), power(q, n)
        check(n <= max(len(pn), len(qn)) - 1,
              "sparse_rational_powers", "uniform power bound")
        check(not is_monomial_ratio(pn, qn),
              "sparse_rational_powers", "nonmonomial powers remain nonmonomial")

    for n in range(1, 21):
        p = power({(0,): F(1), (1,): F(1)}, n)
        q = power({(0,): F(1), (1,): F(-1)}, n)
        check(len(p) - 1 == n, "sharpness", "binomial numerator")
        check(max(len(p), len(q)) - 1 == n, "sharpness", "binomial fraction")

    # Finite polynomial abc checks, with exact gcd reduction.
    for _ in range(80):
        a, b = nonnegative_poly(RNG.randint(1, 5)), nonnegative_poly(RNG.randint(0, 4))
        g = gcd_poly(a, b)
        a, ra = divmod_poly(a, g)
        b, rb = divmod_poly(b, g)
        c = add(a, b)
        check(not ra and not rb, "polynomial_abc", "exact gcd division")
        if c and max(degree(a), degree(b), degree(c)) > 0:
            bound = radical_degree(a) + radical_degree(b) + radical_degree(c) - 1
            check(max(degree(a), degree(b), degree(c)) <= bound,
                  "polynomial_abc", "radical degree inequality")

    for _ in range(80):
        d = RNG.randint(1, 5)
        p, q = nonnegative_poly(d), nonnegative_poly(RNG.randint(0, d - 1))
        g = gcd_poly(p, q)
        p, _ = divmod_poly(p, g)
        q, _ = divmod_poly(q, g)
        quartic = add(power(p, 4), power(q, 4))
        check(square_root_poly(quartic) is None, "quartic_finite_tests",
              "nonconstant rational input has no rational square root")

    matrices = [((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 1), (0, 1)),
                ((1, 0), (1, 1)), ((-1, 0), (0, 1)), ((1, -2), (0, 1))]
    bases_choices = [(F(-1), F(1)), (F(2), F(3)), (F(1, 2), F(-1)), (F(1), F(1))]
    for _ in range(100):
        p = random_poly(2, RNG.randint(1, 5))
        a, b = RNG.choice(matrices), RNG.choice(matrices)
        chi, eta = RNG.choice(bases_choices), RNG.choice(bases_choices)
        combined = tuple(eta[j] * character(chi, matvec(b, tuple(int(i == j) for i in range(2))))
                         for j in range(2))
        check(transform(transform(p, b, eta), a, chi)
              == transform(p, matmul(a, b), combined),
              "automorphism_composition", "semilinear rule with identity coefficient action")
        inv = inverse_matrix(a)
        inv_bases = tuple(1 / character(chi, matvec(inv, tuple(int(i == j) for i in range(2))))
                          for j in range(2))
        check(transform(transform(p, a, chi), inv, inv_bases) == p,
              "automorphism_inverse", "inverse character convention")

    # Conic contrast, exact Laurent arithmetic.
    x = {(1,): F(1, 2), (-1,): F(-1, 2)}
    y = {(1,): F(1, 2), (-1,): F(1, 2)}
    check(power(y, 2) == add({(0,): F(1)}, power(x, 2)),
          "boundary_examples", "conic parametrization")

    for n in range(2, 9):
        for cutoff in range(3, 11):
            coefficient = F(1)
            series: Poly = {(0,): coefficient}
            for j in range(1, cutoff + 1):
                coefficient *= (F(1, n) - (j - 1)) / j
                series[(j,)] = coefficient
            check(power(series, n, cutoff) == {(0,): F(1), (1,): F(1)},
                  "truncated_hahn_roots", "formal binomial identity modulo T^(N+1)")

    for p in [2, 3, 5, 7]:
        for r in range(1, 4):
            n = p ** r
            check(all(math.comb(n, j) % p == 0 for j in range(1, n)),
                  "boundary_examples", "Frobenius sparse-power failure")
        check(all(math.comb(p, j) % p == 0 for j in range(1, p)),
              "boundary_examples", "compatibility of prime-local translation")

    # Directly test the binomial coefficients for the quartic failure in char 2.
    check(math.comb(2, 1) % 2 == 0, "boundary_examples", "(1+x^2)^2=1+x^4 in char 2")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("verification.json"))
    args = parser.parse_args()
    start = time.perf_counter()
    report = {"seed": 20260923, "python": platform.python_version(),
              "arithmetic": "exact integers and fractions; Python standard library",
              "scope": "Finite algebra checks only; not formal verification of the theorems"}
    try:
        run_checks()
        report["status"] = "PASS"
    except Exception as exc:
        report["status"] = "FAIL"
        report["error"] = repr(exc)
        raise
    finally:
        report["checks_by_category"] = dict(sorted(COUNTS.items()))
        report["total_checks"] = sum(COUNTS.values())
        report["elapsed_seconds"] = round(time.perf_counter() - start, 3)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
