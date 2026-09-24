#!/usr/bin/env python3
"""Exact finite checks for Arithmetic Sampling in Surreal Hahn Fields.

Requires Python 3.9+ and SymPy 1.14 (tested with 1.14.0).
These checks do not prove infinite summability, flatness, or undecidability.
No network, repository access, or proof assistant is used.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import platform
import random
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
from typing import Dict, Iterable

import sympy as sp

Hahn = Dict[int, Q]
X, Y, Z = sp.symbols("X Y Z")
COUNTS: Dict[str, int] = defaultdict(int)
RNG = random.Random(20260923)


def check(group: str, condition: bool, message: str = "") -> None:
    if not condition:
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] += 1


def clean(a: Hahn) -> Hahn:
    return {e: Q(c) for e, c in a.items() if c}


def add(a: Hahn, b: Hahn) -> Hahn:
    c = defaultdict(Q, a)
    for e, b_e in b.items():
        c[e] += b_e
    return clean(dict(c))


def scale(a: Hahn, c: Q) -> Hahn:
    return clean({e: c * a_e for e, a_e in a.items()})


def mul(a: Hahn, b: Hahn) -> Hahn:
    c = defaultdict(Q)
    for e, a_e in a.items():
        for f, b_f in b.items():
            c[e + f] += a_e * b_f
    return clean(dict(c))


def power(a: Hahn, n: int) -> Hahn:
    if n < 0:
        raise ValueError("This finite polynomial helper only handles nonnegative powers")
    result: Hahn = {0: Q(1)}
    for _ in range(n):
        result = mul(result, a)
    return result


def binomial_hahn(a: Hahn, n: int) -> Hahn:
    result: Hahn = {0: Q(1)}
    for j in range(n):
        result = mul(result, add(a, {0: Q(-j)}))
    return scale(result, Q(1, math.factorial(n)))


def random_hahn(omnific: bool = False) -> Hahn:
    a = {e: Q(RNG.randint(-3, 3), RNG.randint(1, 3)) for e in range(-3, 4)}
    if omnific:
        a = {e: c for e, c in a.items() if e < 0}
        a[0] = Q(RNG.randint(-4, 4))
    return clean(a)


def ct(a: Hahn) -> Q:
    return a.get(0, Q(0))


def in_B(a: Hahn) -> bool:
    return all(e <= 0 for e in a)


def in_A(a: Hahn) -> bool:
    return in_B(a) and ct(a).denominator == 1


def sQ(c: Q) -> sp.Rational:
    return sp.Rational(c.numerator, c.denominator)


def degree(p: sp.Expr, *variables: sp.Symbol) -> int:
    return -1 if sp.expand(p) == 0 else int(sp.Poly(p, *variables).total_degree())


def monic_gcd(polynomials: Iterable[sp.Expr]) -> sp.Expr:
    g = sp.Poly(0, Z, domain=sp.QQ)
    for p in polynomials:
        g = sp.gcd(g, sp.Poly(p, Z, domain=sp.QQ))
    return sp.expand(g.monic().as_expr()) if not g.is_zero else sp.Integer(0)


def random_poly(max_degree: int = 5) -> sp.Expr:
    return sp.expand(sum(
        RNG.randint(-3, 3) * X**i * Y**j
        for i in range(max_degree + 1)
        for j in range(max_degree + 1 - i)
        if RNG.randrange(3) == 0
    ))


def test_scale_extraction() -> None:
    group = "scale_extraction_and_evaluation"
    for _ in range(30):
        powers = {(i, j): random_hahn() for i in range(4) for j in range(4 - i)}
        scales: Dict[int, sp.Expr] = defaultdict(lambda: sp.Integer(0))
        for (i, j), coefficient in powers.items():
            for e, c in coefficient.items():
                scales[e] += sQ(c) * X**i * Y**j
        for sx, sy in [(-2, 1), (0, 0), (1, 1), (2, -1), (Q(1, 2), Q(-2, 3))]:
            sx, sy = Q(sx), Q(sy)
            evaluated: Hahn = {}
            for (i, j), coefficient in powers.items():
                evaluated = add(evaluated, scale(coefficient, sx**i * sy**j))
            from_scales = {
                e: Q(p.subs({X: sQ(sx), Y: sQ(sy)})) for e, p in scales.items()
            }
            check(group, evaluated == clean(from_scales), "coefficient extraction commutes with evaluation")
            tail_zero = all(p.subs({X: sQ(sx), Y: sQ(sy)}) == 0
                            for e, p in scales.items() if e > 0)
            check(group, in_B(evaluated) == tail_zero, "full positive-tail test")
            p0 = scales.get(0, sp.Integer(0)).subs({X: sQ(sx), Y: sQ(sy)})
            check(group, in_A(evaluated) == (tail_zero and Q(p0).denominator == 1), "residue condition")


def test_pullback_and_binomials() -> None:
    group = "constant_term_pullback_and_omnific_binomials"
    for _ in range(70):
        a, b = random_hahn(True), random_hahn(True)
        check(group, in_A(add(a, b)))
        check(group, in_A(mul(a, b)))
        check(group, ct(mul(a, b)) == ct(a) * ct(b))
        for n in range(7):
            c = binomial_hahn(a, n)
            check(group, in_A(c), "binomial preserves finite model of canonical integer part")
            check(group, ct(c) == Q(sp.binomial(int(ct(a)), n)))
    check(group, not in_A({-1: Q(1), 1: Q(1)}), "leading magnitude is insufficient")
    check(group, sp.expand((sp.I * (sp.I - 1)) / 2) == (-1-sp.I)/2)
    check(group, not bool(sp.re((-1-sp.I)/2).is_integer))


def test_finite_differences() -> None:
    group = "multivariate_newton_coefficients"
    for _ in range(20):
        basis = {(i, j): random_hahn(True) for i in range(4) for j in range(4)}

        def evaluate(x: int, y: int) -> Hahn:
            value: Hahn = {}
            for (i, j), b in basis.items():
                bx = math.comb(x, i) if x >= i else 0
                by = math.comb(y, j) if y >= j else 0
                value = add(value, scale(b, Q(bx * by)))
            return value

        values = {(x, y): evaluate(x, y) for x in range(5) for y in range(5)}
        for a in range(5):
            for b in range(5):
                difference: Hahn = {}
                for i in range(a + 1):
                    for j in range(b + 1):
                        weight = (-1)**(a+b-i-j) * math.comb(a, i) * math.comb(b, j)
                        difference = add(difference, scale(values[i, j], Q(weight)))
                check(group, difference == basis.get((a, b), {}), "finite Newton reconstruction")
                check(group, in_A(difference))


def test_groebner_reduction() -> None:
    group = "graded_groebner_and_scale_normal_forms"
    original = [Y-X**2, X**3-X]
    basis = sp.groebner(original, X, Y, order="grlex", domain=sp.QQ)
    generators = [p.as_expr() for p in basis.polys]
    for _ in range(45):
        f = random_poly(6)
        quotients, remainder = basis.reduce(f)
        reconstruction = sum(q*g for q, g in zip(quotients, generators)) + remainder
        check(group, sp.expand(f-reconstruction) == 0, "division identity")
        check(group, degree(remainder, X, Y) <= degree(f, X, Y), "normal form does not increase degree")
        for q, g in zip(quotients, generators):
            check(group, degree(q*g, X, Y) <= degree(f, X, Y), "reduction products have bounded degree")
        check(group, basis.reduce(remainder)[1] == remainder, "normal form idempotence")
        for s in [-1, 0, 1]:
            check(group, sp.expand(f-remainder).subs({X: s, Y: s*s}) == 0)
        h1, h2 = random_poly(3), random_poly(3)
        member = sp.expand(original[0]*h1 + original[1]*h2)
        check(group, basis.reduce(member)[1] == 0, "known ideal image")
    for _ in range(15):
        scale_polynomials = {e: random_poly(4) for e in range(-3, 6)}
        reduced = {e: basis.reduce(p)[1] for e, p in scale_polynomials.items()}
        for e in scale_polynomials:
            check(group, basis.reduce(scale_polynomials[e] - reduced[e])[1] == 0)
            check(group, degree(reduced[e], X, Y) <= degree(scale_polynomials[e], X, Y))


def test_matrix_syzygies() -> None:
    group = "polynomial_matrix_relations"
    M = sp.Matrix([[X, Y, 0], [0, X, Y]])
    h = sp.Matrix([Y**2, -X*Y, X**2])
    check(group, M*h == sp.zeros(2, 1), "explicit polynomial syzygy")
    for _ in range(40):
        scales = {e: random_poly(3) for e in range(-2, 4)}
        for e, p in scales.items():
            U = h*p
            check(group, all(sp.expand(q) == 0 for q in M*U), f"syzygy at scale {e}")
            check(group, max(degree(q, X, Y) for q in U) <= degree(p, X, Y)+2)
        v = sp.Matrix([random_poly(3) for _ in range(3)])
        f = M*v
        check(group, all(sp.expand(q) == 0 for q in (M*(v+h) - f)))


def test_sharp_gcd_certificates() -> None:
    group = "sharp_actual_scale_gcd_certificates"
    for d in range(7):
        polys = [sp.prod(Z-l for l in range(d+1) if l != j) for j in range(d+1)]
        check(group, all(degree(p, Z) == d for p in polys))
        check(group, monic_gcd(polys) == 1)
        for mask in range(1, 1 << (d+1)):
            selected = [polys[j] for j in range(d+1) if mask & (1 << j)]
            missing = [j for j in range(d+1) if not mask & (1 << j)]
            expected = sp.expand(sp.prod(Z-j for j in missing))
            check(group, monic_gcd(selected) == expected)
    for _ in range(40):
        initial = sp.prod((Z-r)**RNG.randint(1, 3) for r in [-2, 0, 3])
        degree0 = degree(initial, Z)
        current = monic_gcd([initial])
        steps = 1
        for r in RNG.sample([-2, 0, 3], 3):
            candidate = sp.div(current, Z-r, Z)[0]
            new = monic_gcd([current, candidate])
            if new != current:
                steps += 1
            check(group, degree(new, Z) < degree(current, Z))
            current = new
        check(group, steps <= degree0+1)


def test_jets() -> None:
    group = "hasse_derivatives_and_contact_multiplicity"
    for multiplicities in [(1, 2, 3), (2, 2, 2), (3, 1, 4), (1, 1, 1)]:
        roots = [-2, 0, 3]
        H = sp.expand(sp.prod((Z-r)**m for r, m in zip(roots, multiplicities)))
        all_scales = [H, H*(Z+4), H*(Z**2+1)]
        for order in range(1, 7):
            derivatives = [sp.diff(p, Z, j)/math.factorial(j)
                           for p in all_scales for j in range(order)]
            expected = sp.expand(sp.prod((Z-r)**max(m-order+1, 0)
                                         for r, m in zip(roots, multiplicities)))
            check(group, monic_gcd(derivatives) == expected)
            only_selected_scale = [sp.diff(H, Z, j)/math.factorial(j) for j in range(order)]
            check(group, monic_gcd(only_selected_scale) == expected)
            for s in range(-3, 5):
                all_zero = all(p.subs(Z, s) == 0 for p in derivatives)
                multiplicity = multiplicities[roots.index(s)] if s in roots else 0
                check(group, all_zero == (multiplicity >= order))
        for a in range(5):
            P, Qp = H, Z**3+2*Z+1
            left = sp.diff(P*Qp, Z, a)/math.factorial(a)
            right = sum(sp.diff(P, Z, b)*sp.diff(Qp, Z, a-b)
                        / (math.factorial(b)*math.factorial(a-b)) for b in range(a+1))
            check(group, sp.expand(left-right) == 0)


def test_realization() -> None:
    group = "ideal_realization_and_growth_examples"
    ideal_generators = [Y-X**2, X**3-X]
    basis = sp.groebner(ideal_generators, X, Y, order="grlex", domain=sp.QQ)
    scales = {1: ideal_generators[0], 2: ideal_generators[1]}
    for n in range(1, 13):
        scales[n*(n+4)] = sp.expand(X**n * ideal_generators[0])
    extended = sp.groebner(list(scales.values()), X, Y, order="grlex", domain=sp.QQ)
    check(group, list(basis) == list(extended))
    check(group, 0 not in scales)
    for e, p in scales.items():
        check(group, basis.reduce(p)[1] == 0)
    for n in range(1, 13):
        check(group, degree(scales[n*(n+4)], X, Y) == n+2)
    for rho in range(-8, 9):
        vals = [n*(n+4)+(n+2)*rho for n in range(30, 61)]
        check(group, all(b > a for a, b in zip(vals, vals[1:])))
        check(group, vals[-1] > 1000)
    for x, y in itertools.product(range(-2, 3), repeat=2):
        common_zero = all(p.subs({X: x, Y: y}) == 0 for p in scales.values())
        expected = y == x*x and x**3 == x
        check(group, common_zero == expected)


def test_machine_family() -> None:
    group = "bounded_machine_family_and_quadratic_modulus"
    length = 48
    for halt_step in [None, *range(32)]:
        # A finite collection of COMPLETE base blocks, not a truncation of F(1)
        # by power degree. This preserves each block's exact zero at z=1.
        blocks = {(n+1)**2: Z**(n+1)*(Z-1) for n in range(length+1)}
        if halt_step is not None:
            special = (halt_step+2)**2+1
            check(group, math.isqrt(special)**2 != special)
            check(group, special not in blocks)
            blocks[special] = Z**(halt_step+1)
        coefficient_table: Dict[int, Hahn] = defaultdict(dict)
        for e, p in blocks.items():
            for (m,), c in sp.Poly(p, Z).terms():
                coefficient_table[m][e] = Q(c)
        for m in range(1, length+2):
            expected = {1: Q(-1)} if m == 1 else {(m-1)**2: Q(1), m*m: Q(-1)}
            if halt_step == m-1:
                expected[(m+1)**2+1] = Q(1)
            actual = clean(coefficient_table[m])
            check(group, actual == expected)
            check(group, bool(actual) and min(actual) >= (m-1)**2)
        gcd = monic_gcd(blocks.values())
        expected_gcd = Z if halt_step is not None else Z*(Z-1)
        check(group, sp.expand(gcd-expected_gcd) == 0)
        value_at_one = clean({e: Q(p.subs(Z, 1)) for e, p in blocks.items()})
        check(group, in_A(value_at_one) == (halt_step is None))
        for e in [1, 4, 5, 9, 17, 36, 81, 144]:
            safe_bound = 1+math.isqrt(e)
            check(group, all(m <= safe_bound for m, a in coefficient_table.items() if e in a))
        for point in [-2, -1, 0, 1, 2]:
            all_zero = all(p.subs(Z, point) == 0 for p in blocks.values())
            check(group, all_zero == (point == 0 or (point == 1 and halt_step is None)))
    for rho in range(-12, 13):
        weighted = [(m-1)**2 + m*rho for m in range(40, 81)]
        check(group, all(b > a for a, b in zip(weighted, weighted[1:])))


def test_boundaries() -> None:
    group = "boundary_counterexamples_and_finite_products"
    bad_exponents = [-Q(n)-Q(1, n) for n in range(1, 101)]
    check(group, all(b < a for a, b in zip(bad_exponents, bad_exponents[1:])))
    good_exponents = [-Q(1, n) for n in range(1, 101)]
    check(group, all(b > a for a, b in zip(good_exponents, good_exponents[1:])))
    for count in range(1, 13):
        coefficients: Dict[int, Hahn] = {0: {0: Q(1)}}
        for m in range(1, count+1):
            new = {n: dict(a) for n, a in coefficients.items()}
            for n, a in coefficients.items():
                shifted = {e+m: -c for e, c in a.items()}
                new[n+1] = add(new.get(n+1, {}), shifted)
            coefficients = new
        for n in range(count+1):
            check(group, min(coefficients[n]) == n*(n+1)//2)
            check(group, coefficients[n][n*(n+1)//2] == (-1)**n)
        for j in range(1, count+1):
            value: Hahn = {}
            for n, a in coefficients.items():
                value = add(value, {e-j*n: c for e, c in a.items()})
            check(group, value == {}, "finite product has each specified infinite monomial root")
    for sample in [[], [-2], [-2, 0, 3], [-3, -1, 1, 3]]:
        p = sp.sympify(sp.prod(Z-n for n in sample))
        for point in range(-5, 6):
            value = clean({1: Q(p.subs(Z, point))})
            check(group, in_A(value) == (point in sample))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional output JSON; otherwise print only")
    args = parser.parse_args()
    suites = [test_scale_extraction, test_pullback_and_binomials, test_finite_differences,
              test_groebner_reduction, test_matrix_syzygies, test_sharp_gcd_certificates,
              test_jets, test_realization, test_machine_family, test_boundaries]
    for suite in suites:
        suite()
    report = {
        "status": "PASS",
        "seed": 20260923,
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "assertions": dict(COUNTS),
        "total_assertions": sum(COUNTS.values()),
        "scope": "Exact finite algebraic checks; not a proof-assistant certificate or a proof of infinite theorems.",
    }
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
