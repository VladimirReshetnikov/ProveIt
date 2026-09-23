#!/usr/bin/env python3
"""Exact finite regression checks for Ramification in Omnific Normalizations.

These checks exercise finite identities and finite-dimensional analogues.
They are not proofs of integrality, valuation existence, cardinality,
Hahn summability, or the infinite theorems in article.tex.

Requires Python 3.9 or later; standard library only.
Usage: python verify.py [--output verification.json]
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import platform
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from typing import Dict, List, Tuple

Poly = Dict[int, F]
Pair = Tuple[Poly, Poly]


def clean(p: Poly) -> Poly:
    return {e: c for e, c in p.items() if c}


def add(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, F(0)) + c
    return clean(r)


def scale(p: Poly, c: F) -> Poly:
    return clean({e: a * c for e, a in p.items()})


def mul(p: Poly, q: Poly, cutoff: int | None = None) -> Poly:
    r: Poly = {}
    for e, a in p.items():
        for f, b in q.items():
            if cutoff is None or e + f < cutoff:
                r[e + f] = r.get(e + f, F(0)) + a * b
    return clean(r)


def power(p: Poly, n: int, cutoff: int | None = None) -> Poly:
    if n < 0:
        raise ValueError("Polynomial power must be nonnegative")
    r = {0: F(1)}
    while n:
        if n & 1:
            r = mul(r, p, cutoff)
        p = mul(p, p, cutoff)
        n //= 2
    return r


def binomial_coeffs(alpha: F, degree: int) -> List[F]:
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    coefficients = [F(1)]
    for j in range(1, degree + 1):
        coefficients.append(coefficients[-1] * (alpha - j + 1) / j)
    return coefficients


def quadratic_mul(p: Pair, q: Pair, c: F) -> Pair:
    """Multiply a+b*h with h^2=T^2+c, using finite rational polynomials."""
    a, b = p
    d, e = q
    return (
        add(mul(a, d), mul(mul(b, e), {2: F(1), 0: c})),
        add(mul(a, e), mul(b, d)),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification.json"))
    args = parser.parse_args()
    counts: Counter[str] = Counter()

    def check(category: str, condition: bool, context: object) -> None:
        if not condition:
            raise AssertionError(f"{category}: failed for {context!r}")
        counts[category] += 1

    # 1. Binomial powers, exactly modulo X^19.
    degree = 18
    for n in range(2, 21):
        coeffs = binomial_coeffs(F(1, n), degree)
        p = {j: a for j, a in enumerate(coeffs)}
        pn = power(p, n, degree + 1)
        for j in range(degree + 1):
            expected = F(1) if j in (0, 1) else F(0)
            check("binomial_coefficient_identities", pn.get(j, F(0)) == expected,
                  {"n": n, "coefficient": j})
    check("displayed_square_root_coefficients",
          binomial_coeffs(F(1, 2), 4) ==
          [F(1), F(1, 2), F(-1, 8), F(1, 16), F(-5, 128)], "z_2")

    # 2. Exact integer thresholds and the lower boundary.
    for n in range(2, 101):
        for m in range(1, 51):
            j = (n + m - 1) // m
            check("refinement_thresholds", F(m * j, n) >= 1 and
                  (j == 1 or F(m * (j - 1), n) < 1), (n, m, j))
    check("displayed_refinement_table",
          [(12 + m - 1) // m for m in (1, 2, 3, 4, 6, 12)] ==
          [12, 6, 4, 3, 2, 1], "z_12")

    # 3. Finite polynomial certificates for z_n^j / U.
    # y^n = U^(mj-n)*(1+U^(m(n-1)))^j. Test actual polynomials.
    for n in range(2, 16):
        for m in range(1, 13):
            j = (n + m - 1) // m
            exponent = m * j - n
            rhs = mul({exponent: F(1)},
                      power({0: F(1), m * (n - 1): F(1)}, j))
            check("refinement_monic_certificates",
                  min(rhs) >= 0 and rhs.get(0, F(0)) ==
                  (F(1) if exponent == 0 else F(0)), (n, m, j))

    # 4. Quadratic idempotent identities before quotienting.
    for root in range(1, 41):
        c = F(root * root)
        e: Pair = ({0: F(1, 2)}, {0: F(1, 2 * root)})
        e2 = quadratic_mul(e, e, c)
        error = (add(e2[0], scale(e[0], F(-1))),
                 add(e2[1], scale(e[1], F(-1))))
        check("quadratic_idempotent_identities",
              error == ({2: F(1, 4) / c}, {}), root)

    # 5. Finite Boolean partition models. This does not check field independence.
    for r in range(1, 9):
        assignments = list(itertools.product((0, 1), repeat=r))
        for word in assignments:
            evaluations = [int(all(w == a for w, a in zip(word, assignment)))
                           for assignment in assignments]
            check("finite_boolean_words", sum(evaluations) == 1, (r, word))
        for assignment in assignments:
            total = sum(int(all(w == a for w, a in zip(word, assignment)))
                        for word in assignments)
            check("finite_boolean_partitions", total == 1, (r, assignment))

    # 6. Basis-level kernel/image equality in Q[X]/(X^n).
    # Not an independent proof of the infinite normalization-fibre resolution.
    for n in range(2, 41):
        for j in range(1, n):
            kernel = {a for a in range(n) if a + j >= n}
            image = {a + n - j for a in range(n) if a + n - j < n}
            check("truncated_polynomial_annihilators", kernel == image, (n, j))
            composition_zero = all(
                mul(mul({a: F(1)}, {j: F(1)}, n),
                    {n - j: F(1)}, n) == {} for a in range(n))
            check("alternating_compositions", composition_zero, (n, j))
        check("tensor_differentials_vanish",
              mul({0: F(1)}, {1: F(1)}, 1) == {} and
              mul({0: F(1)}, {n - 1: F(1)}, 1) == {}, n)

    # 7. Compositional law for clipped positive rational orders.
    for q in range(1, 31):
        for p in range(q + 1):
            h = F(p, q)
            for m in (1, 2, 3, 5, 8):
                for n in (1, 2, 4, 7):
                    lhs = min(F(1), n * min(F(1), m * h))
                    rhs = min(F(1), n * m * h)
                    check("clipped_refinement_composition", lhs == rhs,
                          (str(h), m, n))

    tex = Path(__file__).with_name("article.tex")
    report = {
        "status": "all finite checks passed",
        "scope": "Exact finite identities and finite-dimensional analogues only; "
                 "not proof-assistant verification of the article's theorems.",
        "python_version": platform.python_version(),
        "dependencies": "Python standard library only",
        "repository_baseline": "343dc2c471212bb9b53ff4623bace2e1943f255b",
        "counts": dict(sorted(counts.items())),
        "total_checks": sum(counts.values()),
        "article_tex_sha256": hashlib.sha256(tex.read_bytes()).hexdigest()
                              if tex.exists() else None,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
