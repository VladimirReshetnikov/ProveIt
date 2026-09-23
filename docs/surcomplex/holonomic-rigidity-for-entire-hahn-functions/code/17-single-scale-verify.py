#!/usr/bin/env python3
"""Exact finite regression checks for article.tex.

These tests check finite proof mechanisms, not infinite theorems.  They never
numerically approximate a surreal number.  Sparse exponents are ordinary exact
integers, even when factorially large.  Requires Python 3.10+ and SymPy.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations_with_replacement, product
from math import factorial
from pathlib import Path
import json
import platform
import sys
import sympy as sp

Sparse = dict[tuple[int, int], Fraction]  # (q exponent, z exponent) -> coefficient
COUNTS: Counter[str] = Counter()


def check(condition: bool, group: str, message: str) -> None:
    if not condition:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] += 1


def add(*polys: Sparse) -> Sparse:
    out: Sparse = {}
    for poly in polys:
        for monomial, coefficient in poly.items():
            out[monomial] = out.get(monomial, Fraction(0)) + coefficient
    return {m: c for m, c in out.items() if c}


def scale(poly: Sparse, scalar: int | Fraction) -> Sparse:
    return {m: c * scalar for m, c in poly.items() if c * scalar}


def mul(a: Sparse, b: Sparse) -> Sparse:
    out: Sparse = {}
    for (aq, az), ac in a.items():
        for (bq, bz), bc in b.items():
            key = (aq + bq, az + bz)
            out[key] = out.get(key, Fraction(0)) + ac * bc
    return {m: c for m, c in out.items() if c}


def shift(a: Sparse, q: int = 0, z: int = 0) -> Sparse:
    return {(eq + q, ez + z): c for (eq, ez), c in a.items()}


def jet(a: Sparse, theta_order: int = 0, delta_order: int = 0) -> Sparse:
    return {m: c * m[1] ** theta_order * m[0] ** delta_order
            for m, c in a.items()
            if c * m[1] ** theta_order * m[0] ** delta_order}


def family(indices: list[int], *, numerical: bool = False,
           quadratic: bool = False) -> Sparse:
    return {(n * n if quadratic else factorial(n), 0 if numerical else n):
            Fraction(1) for n in indices}


def test_separation() -> None:
    for degree in (1, 2, 3):
        threshold = max(3, 4 * degree)
        targets = list(combinations_with_replacement(
            range(threshold, threshold + 3), degree))
        candidates = [u for d in range(degree + 1)
                      for u in combinations_with_replacement(
                          range(2, threshold + 4), d)]
        bound = factorial(threshold) // 2
        for target in targets:
            target_height = sum(map(factorial, target))
            for other in candidates:
                if target == other:
                    continue
                distance = abs(target_height - sum(map(factorial, other)))
                check(distance >= bound, "height_separation",
                      f"D={degree}, target={target}, other={other}")
    check(3 * factorial(2) == factorial(3), "necessary_threshold",
          "small-index collision must be retained")


def monomial_vectors(total: int, length: int):
    for vector in product(range(total + 1), repeat=length):
        if sum(vector) == total:
            yield vector


def test_polarization() -> None:
    for dimension, weights in ((1, ((0,), (1,), (2,))),
                               (2, ((0, 0), (1, 0), (0, 1), (1, 1)))):
        for degree in (1, 2, 3):
            u = sp.symbols(f"u0:{degree}")
            x = [sp.symbols(f"x{j}_0:{dimension}") for j in range(degree)]
            substitutions = [sum(u[j] * sp.prod(
                x[j][d] ** alpha[d] for d in range(dimension))
                for j in range(degree)) for alpha in weights]
            seen = set()
            for powers in monomial_vectors(degree, len(weights)):
                expr = sp.prod(y ** p for y, p in zip(substitutions, powers))
                polarized = sp.Poly(sp.expand(expr), *u).coeff_monomial((1,) * degree)
                check(polarized != 0, "polarization", str(powers))
                support = set(sp.Poly(polarized, *sum((list(t) for t in x), [])).monoms())
                check(not (support & seen), "polarization_orbits", str(powers))
                seen.update(support)
    x, y = sp.symbols("x y")
    check(sp.expand(x*x+y*y-2*x*y-(x-y)**2) == 0,
          "polarization_cancellation", "quadratic example")


def test_coefficient_witnesses() -> list[dict]:
    f = family(list(range(2, 15)))
    q2 = add(mul(f, jet(f, 2)), scale(mul(jet(f, 1), jet(f, 1)), -1))
    h = factorial(8) + factorial(9)
    check(q2.get((h, 17)) == 1, "coefficient_witnesses", "pure Euler quadratic")
    mixed = add(mul(f, jet(f, 1, 1)), scale(mul(jet(f, 0, 1), jet(f, 1, 0)), -1))
    expected = (8 - 9) * (factorial(8) - factorial(9))
    expression = add(mixed, shift(mixed, q=3), shift(f, q=2, z=4))
    check(expression.get((h, 17)) == expected, "coefficient_witnesses", "mixed band start")
    check(expression.get((h + 3, 17)) == expected, "coefficient_witnesses", "mixed shifted band")
    a = family(list(range(2, 16, 2)))
    b = family(list(range(3, 16, 2)))
    cubic = mul(add(mul(a, jet(a, 2)), scale(mul(jet(a, 1), jet(a, 1)), -1)), b)
    height = factorial(12) + factorial(14) + factorial(13)
    check(cubic.get((height, 39)) == 4, "coefficient_witnesses", "two-colour cubic")
    s = family(list(range(2, 15)), numerical=True)
    sq = add(mul(s, jet(s, 0, 2)), scale(mul(jet(s, 0, 1), jet(s, 0, 1)), -1))
    check(sq.get((h, 0)) == (factorial(8) - factorial(9)) ** 2,
          "coefficient_witnesses", "numerical Euler quadratic")
    for orders in product(range(4), repeat=4):
        a1, b1, a2, b2 = orders
        check(jet(jet(f, a1, b1), a2, b2) == jet(f, a1+a2, b1+b2),
              "commuting_jets", str(orders))
    return [
        {"expression": "F*Theta^2(F)-Theta(F)^2", "q_exponent": h,
         "z_exponent": 17, "coefficient": 1},
        {"expression": "(1+q^3)*(F*Theta*delta(F)-delta(F)*Theta(F))+q^2*z^4*F",
         "q_exponent": h, "z_exponent": 17, "coefficient": expected},
        {"expression": "(A*Theta^2(A)-Theta(A)^2)*B; A even, B odd",
         "q_exponent": height, "z_exponent": 39, "coefficient": 4},
    ]


def test_patterns() -> None:
    v = sp.Matrix([[1, 0, 1], [0, 1, 1], [1, 1, 1], [0, 0, 1]])
    relation = sp.Matrix([[-1, -1, 1, 1]])
    check(v.rank() == 3, "finite_patterns", "union/intersection rank")
    check(relation * v == sp.zeros(1, 3), "finite_patterns", "exact linear relation")
    for r, s in product(range(4), range(3)):
        block = sp.kronecker_product(sp.eye((r+1)*(s+1)), v)
        check(block.rank() == 3*(r+1)*(s+1), "jet_block_rank", f"r={r},s={s}")
    indices = set(range(2, 15))
    a = {n for n in indices if n % 3 in (0, 2)}
    b = {n for n in indices if n % 3 in (1, 2)}
    lhs = add(family(sorted(a | b)), family(sorted(a & b)))
    rhs = add(family(sorted(a)), family(sorted(b)))
    check(lhs == rhs, "finite_patterns", "union/intersection sparse identity")
    c = a ^ {2}
    diff = add(family(sorted(c)), scale(family(sorted(a)), -1))
    check(diff == {(factorial(2), 2): Fraction(-1)}, "finite_patterns", "finite correction")
    # Full-row-rank substitution has a rational right inverse.
    rref, pivots = v.T.rref()
    independent_rows = list(pivots)
    w = v[independent_rows, :]
    check(w.det() != 0, "finite_patterns", "coordinate selection")
    check(w * w.inv() == sp.eye(3), "finite_patterns", "explicit right inverse")


def prefix_index(period: tuple[int, ...], level: int) -> int:
    value = 1
    for i in range(level):
        value = 2 * value + period[i % len(period)]
    return value


def test_prefixes() -> None:
    periods = ((0,), (1,), (0, 1), (1, 0))
    sets = [{prefix_index(p, ell) for ell in range(1, 11)} for p in periods]
    for i, p in enumerate(periods):
        for ell in range(1, 11):
            n = prefix_index(p, ell)
            check(2**ell <= n < 2**(ell+1), "binary_prefixes", f"p={p}, level={ell}")
            if ell >= 3:
                check(all(n not in sets[j] for j in range(len(sets)) if j != i),
                      "private_prefixes", f"p={p}, level={ell}")
    for i in range(len(sets)):
        for j in range(i):
            check(all(n < 8 for n in sets[i] & sets[j]), "binary_prefixes", "finite common prefix")


def test_intrinsic_jets() -> None:
    x = sp.Symbol("x")
    for order in range(9):
        poly = sp.Poly(sp.prod(x + h for h in range(order)), x)
        check(poly.LC() == 1, "intrinsic_triangular", f"order={order}")
        for n in range(-4, 13):
            coefficient, exponent = 1, n
            for _ in range(order):
                coefficient *= -exponent
                exponent += 1
            expected = (-1)**order
            for h in range(order):
                expected *= n + h
            check(coefficient == expected and exponent == n + order,
                  "intrinsic_monomials", f"n={n},order={order}")
    # Stirling conversion on ordinary integer monomial powers.
    stirling = [[0] * 9 for _ in range(9)]
    stirling[0][0] = 1
    for r in range(1, 9):
        for j in range(1, r+1):
            stirling[r][j] = stirling[r-1][j-1] + j*stirling[r-1][j]
    for n in range(16):
        for r in range(9):
            total = 0
            for j in range(r+1):
                falling = 1
                for h in range(j):
                    falling *= n-h
                total += stirling[r][j]*falling
            check(total == n**r, "Euler_conversion", f"n={n},r={r}")


def test_domain_and_codes() -> None:
    # Lexicographic pairs represent coefficients of an infinite unit and of 1.
    for n in range(2, 18):
        for m in range(0, 8):
            if n*factorial(n) > m:
                check(factorial(n+1)-(n+1)*m > factorial(n)-n*m,
                      "finite_valuation_domain", f"n={n},m={m}")
        negative_infinite = (-n, factorial(n))
        next_negative = (-n-1, factorial(n+1))
        check(next_negative < negative_infinite, "exterior_domain_obstruction", str(n))
        code_exponent = (1, -factorial(n))
        next_code = (1, -factorial(n+1))
        check((0, 0) < next_code < code_exponent, "omnific_code_support", str(n))
    for j, ell in product(range(4), repeat=2):
        if j != ell:
            for n, m in product(range(2, 8), repeat=2):
                check((j, -factorial(n)) != (ell, -factorial(m)),
                      "coding_scale_cosets", f"j={j},ell={ell},n={n},m={m}")
    theta = family(list(range(2, 18)), quadratic=True)
    check(jet(theta, 0, 1) == jet(theta, 2, 0), "polynomial_height_obstruction", "heat equation")


def test_floors() -> list[dict]:
    expected = {0: {}, 1: {0: 1}, 2: {2: 1, 0: 1}, 3: {4: 1, 3: 1},
                6: {12: 1, 10: 1, 0: 1}}
    records = []
    for a, target in expected.items():
        result: Counter[int] = Counter()
        for n in range(2, 11):
            exponent = a*n-factorial(n)
            retained = factorial(n-1) <= a
            check((exponent >= 0) == retained, "floor_cutoffs", f"a={a},n={n}")
            if retained:
                result[exponent] += 1
        check(dict(result) == target, "floor_examples", f"a={a}")
        records.append({"a": a, "nonnegative_exponents": dict(result)})
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    test_separation()
    test_polarization()
    witnesses = test_coefficient_witnesses()
    test_patterns()
    test_prefixes()
    test_intrinsic_jets()
    test_domain_and_codes()
    floors = test_floors()
    result = {
        "status": "passed", "total_checks": sum(COUNTS.values()),
        "groups": dict(sorted(COUNTS.items())),
        "python_version": platform.python_version(), "sympy_version": sp.__version__,
        "scope": "Exact finite regression checks only; not proofs of the infinite theorems.",
        "sparse_coefficient_witnesses": witnesses, "floor_examples": floors,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, ValueError) as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        raise SystemExit(1)
