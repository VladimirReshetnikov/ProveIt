#!/usr/bin/env python3
"""Exact finite diagnostics for article.tex; not a formal proof of its theorems.

Run with Python 3.10+ and SymPy. Results are written next to this script.
No files outside that directory are modified. No network access is used.
"""
from __future__ import annotations

import itertools
import json
import platform
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Callable

import sympy as sp

ROOT = Path(__file__).resolve().parent
T, r, s0, s1, q = sp.symbols("T r s0 s1 q")
results: list[dict[str, object]] = []


def record(name: str, checks: int, description: str) -> None:
    results.append({"name": name, "passed_assertions": checks, "description": description})


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def quadratic_reduce(expr: sp.Expr, variables: tuple[sp.Symbol, ...],
                     radicands: tuple[sp.Expr, ...]) -> sp.Expr:
    """Reduce a polynomial by independent monic equations variable**2=radicand."""
    if len(variables) != len(radicands):
        raise ValueError("Each variable must have exactly one radicand")
    poly = sp.Poly(sp.expand(expr), *variables)
    out = sp.Integer(0)
    for exponents, coefficient in poly.terms():
        term = coefficient
        for variable, radicand, exponent in zip(variables, radicands, exponents):
            term *= radicand ** (exponent // 2) * variable ** (exponent % 2)
        out += term
    return sp.factor(out)


def check_branch_identities() -> None:
    w = (1 - s0 * s1) / 2
    a = T**2 - 1
    b = T**2 / 4 - 1
    require(quadratic_reduce(w*w - w - (T**4 - 5*T**2)/16,
                            (s0, s1), (a, b)) == 0, "two-branch identity")
    general_b = T**2 / r**2 - 1
    rhs = (T**4/r**2 - (1+r**-2)*T**2)/4
    require(quadratic_reduce(w*w - w - rhs,
                            (s0, s1), (a, general_b)) == 0, "general branch identity")
    require(sp.simplify(w.subs({s0: sp.I, s1: sp.I})) == 1, "theta-plus")
    require(sp.simplify(w.subs({s0: sp.I, s1: -sp.I})) == 0, "theta-minus")
    for value in (sp.Rational(2), sp.Rational(3), sp.Rational(5, 2)):
        require(sp.simplify(rhs.subs(r, value).subs(T, 0)) == 0,
                "constant term of branch equation")
    record("quadratic_identities", 7,
           "Exact reductions modulo the defining quadratic equations and branch specializations.")


def check_multiquadratic_patterns() -> None:
    parameters = (sp.Integer(1), sp.Integer(2), sp.Integer(3),
                  sp.Rational(5, 2), sp.Integer(7))
    checks = 0
    # Test the divisor witness used in the square-class proof: every selected
    # radicand contributes its own simple zero in every nonempty finite product.
    for bits in itertools.product((0, 1), repeat=len(parameters)):
        chosen = [value for bit, value in zip(bits, parameters) if bit]
        if not chosen:
            continue
        polynomial = sp.prod(T*T/value**2 - 1 for value in chosen)
        for value in chosen:
            require(polynomial.subs(T, value) == 0, "selected zero")
            require(sp.diff(polynomial, T).subs(T, value) != 0, "simple zero")
            checks += 2
    for bits in itertools.product((0, 1), repeat=len(parameters)-1):
        s0_image = sp.I
        images = [sp.I if bit else -sp.I for bit in bits]
        actual = tuple(sp.simplify((1-s0_image*image)/2) for image in images)
        require(actual == bits, "independent branch assignment")
        checks += 1
    record("multiquadratic_finite_examples", checks,
           "Simple-zero witnesses for 31 nonempty radicand products and all 16 four-branch assignments.")


def check_laurent_coefficients() -> None:
    # Multiplying by q^2 removes negative powers: W=q^2*w.
    W = sp.series(q**2/2 - sp.sqrt((1-q**2)*(1-4*q**2))/4,
                  q, 0, 16).removeO()
    expected = {0: -sp.Rational(1, 4), 2: sp.Rational(9, 8),
                4: sp.Rational(9, 32), 6: sp.Rational(45, 64)}
    checks = 0
    for power, coefficient in expected.items():
        require(W.coeff(q, power) == coefficient, "Laurent coefficient")
        checks += 1
    remainder = sp.expand(W*W - q*q*W - (1-5*q*q)/16)
    for power in range(16):
        require(remainder.coeff(q, power) == 0, "truncated Laurent equation")
        checks += 1
    record("formal_laurent_initial_segment", checks,
           "Initial coefficients of q^2*w and the defining identity through degree 15; no convergence claim.")


def boolean_reduce(expr: sp.Expr, variables: tuple[sp.Symbol, ...]) -> sp.Expr:
    out = sp.Integer(0)
    for exponents, coefficient in sp.Poly(sp.expand(expr), *variables).terms():
        term = coefficient
        for variable, exponent in zip(variables, exponents):
            if exponent:
                term *= variable
        out += term
    return sp.expand(out)


def check_boolean_algebra() -> None:
    a, b = sp.symbols("a b")
    d = a+b-2*a*b
    require(boolean_reduce(d*d-d, (a,b)) == 0, "symmetric difference idempotence")
    require(sp.expand(d.subs(b,a)).subs(a*a,a) == 0, "equal-image kernel")
    require(d.subs({a:1,b:0}) == 1, "nonzero Boolean symmetric difference")
    checks = 3
    # Atom values form an identity matrix. This exactly checks partition,
    # nonvanishing, orthogonality, and finite interpolation on these examples.
    for n in range(1,7):
        words = tuple(itertools.product((0,1), repeat=n))
        for point in words:
            values = tuple(int(all(x==y for x,y in zip(point,word))) for word in words)
            require(sum(values) == 1, "partition of one")
            checks += 1
            for word, value in zip(words, values):
                require(value == int(word == point), "Boolean atom evaluation")
                checks += 1
        require(len(set(words)) == 2**n, "distinct atom assignments")
        checks += 1
    record("finite_boolean_tables", checks,
           "Boolean atoms in 1 through 6 variables, and the exact symmetric-difference polynomial.")


Support = dict[tuple[int,int], Fraction]


def multiply(left: Support, right: Support) -> Support:
    out: defaultdict[tuple[int,int], Fraction] = defaultdict(Fraction)
    for (g,h), a in left.items():
        for (u,v), b in right.items():
            out[(g+u,h+v)] += a*b
    return {index: value for index,value in out.items() if value}


def project(series: Support) -> Support:
    """Projection onto the subgroup Z x {0} of Z^2."""
    return {index:value for index,value in series.items() if index[1] == 0}


def check_support_projection() -> None:
    checks = 0
    coefficients = (-2,-1,0,1,2)
    for a,b,c in itertools.product(coefficients, repeat=3):
        x = {(1,0): Fraction(a), (-2,0): Fraction(b), (0,0): Fraction(c)}
        x = {index:value for index,value in x.items() if value}
        for shift in range(-3,4):
            z = {(2,shift):Fraction(2), (-1,0):Fraction(-3), (0,-1):Fraction(1,2)}
            require(project(multiply(z,x)) == multiply(project(z),x),
                    "subgroup-linear projection")
            checks += 1
    outside = {(0,1):Fraction(1)}
    inverse = {(0,-1):Fraction(1)}
    require(project(multiply(outside,inverse)) != multiply(project(outside),project(inverse)),
            "projection must not be treated as a ring homomorphism")
    checks += 1
    record("finite_support_projection", checks,
           "875 coefficient/shift examples of subgroup linearity and one counterexample to multiplicativity.")


def main() -> None:
    tests: tuple[Callable[[], None], ...] = (
        check_branch_identities, check_multiquadratic_patterns,
        check_laurent_coefficients, check_boolean_algebra, check_support_projection)
    for test in tests:
        test()
    report = {
        "status": "all finite checks passed",
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "total_passed_assertions": sum(int(row["passed_assertions"]) for row in results),
        "groups": results,
        "not_verified": ["proper-class or universe arguments", "full Hahn support theorems",
                         "integrality or ideal membership of arbitrary surreal elements",
                         "the complete article in a proof assistant", "historical novelty"]}
    path = ROOT / "verification_results.json"
    path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
