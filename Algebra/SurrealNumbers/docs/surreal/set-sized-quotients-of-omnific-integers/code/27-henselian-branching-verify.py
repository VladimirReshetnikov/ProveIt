#!/usr/bin/env python3
"""Exact finite checks accompanying the henselian-branching article.

These checks are not proofs of the support, transfinite, or henselization
statements. They test polynomial identities and finite models only.
Run from the package root: python code/verify.py --output data/verification.json
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Callable

import sympy as sp


class Checks:
    def __init__(self) -> None:
        self.counts: dict[str, int] = defaultdict(int)

    def check(self, group: str, name: str, condition: object) -> None:
        if not bool(condition):
            raise AssertionError(f"{group}: {name}")
        self.counts[group] += 1


def run_checks() -> dict[str, object]:
    checks = Checks()
    t, r, u, w, h = sp.symbols("T r u w h")
    discriminant = (t**2 - 1) * (t**2 - 4)
    coefficient = (t**4 - 5 * t**2) / 16
    splitter = sp.Rational(1, 2) - r / 4
    defining = sp.expand(splitter**2 - splitter - coefficient)
    checks.check("splitter", "quadratic certificate",
                 sp.rem(defining, r**2-discriminant, r) == 0)
    checks.check("splitter", "discriminant identity",
                 sp.expand(discriminant - (4 + 16*coefficient)) == 0)
    checks.check("splitter", "squarefree discriminant",
                 sp.gcd(discriminant, sp.diff(discriminant, t)) == 1)
    for root in (-2, -1, 1, 2):
        checks.check("splitter", f"simple zero {root}",
                     discriminant.subs(t, root) == 0 and
                     sp.diff(discriminant, t).subs(t, root) != 0)
    for root in (0, 1):
        equation = u**2-u-coefficient
        checks.check("splitter", f"specialization {root}",
                     equation.subs({t: 0, u: root}) == 0)
        checks.check("splitter", f"simple residue root {root}",
                     sp.diff(equation, u).subs(u, root) != 0)

    z = sp.symbols("z")
    series = sp.series(sp.Rational(1, 2) -
                       sp.sqrt(1 - 5*z**2 + 4*z**4)/(4*z**2),
                       z, 0, 10).removeO().expand()
    expected = {-2: sp.Rational(-1, 4), 0: sp.Rational(9, 8),
                2: sp.Rational(9, 32), 4: sp.Rational(45, 64),
                6: sp.Rational(981, 512), 8: sp.Rational(5715, 1024)}
    for power, value in expected.items():
        checks.check("Laurent coefficients", f"coefficient {power}",
                     series.coeff(z, power) == value)
    # The truncation through z^8 satisfies the quadratic through degree z^6.
    residual = sp.expand(series**2-series-(z**-4-5*z**-2)/16)
    for power in range(-4, 8):
        checks.check("Laurent coefficients", f"residual coefficient {power}",
                     residual.coeff(z, power) == 0)

    idempotent_numerator = (u-w)**2-(u-w)*(1-2*w)
    checks.check("generic idempotent", "difference of defining polynomials",
                 sp.expand(idempotent_numerator - ((u**2-u)-(w**2-w))) == 0)
    e = (u-w)/(1-2*w)
    checks.check("generic idempotent", "first root maps to zero", e.subs(u, w) == 0)
    checks.check("generic idempotent", "second root maps to one",
                 sp.cancel(e.subs(u, 1-w)-1) == 0)
    checks.check("complexification", "square root of minus one numerator",
                 sp.expand((2*u-1)**2 + (4*h-1) - 4*(u**2-u+h)) == 0)
    checks.check("complexification", "negative discriminant model",
                 (1-4*h).subs(h, sp.Rational(5, 4)) < 0)

    atom_rows = 0
    for n in range(1, 7):
        patterns = tuple(itertools.product((0, 1), repeat=n))
        for values in patterns:
            atom_values = []
            for pattern in patterns:
                atom = 1
                for value, bit in zip(values, pattern):
                    atom *= value if bit else 1-value
                checks.check("Boolean atoms", f"{n} variables, {values}, {pattern}",
                             atom == int(values == pattern))
                atom_values.append(atom)
            checks.check("Boolean atoms", f"partition of unity {n}, {values}",
                         sum(atom_values) == 1)
            atom_rows += 1

    # Finite support analogue of F_G-linearity of support projection.
    Exponent = tuple[int, int]
    Polynomial = dict[Exponent, Fraction]

    def clean(p: Polynomial) -> Polynomial:
        return {exponent: value for exponent, value in p.items() if value}

    def multiply(p: Polynomial, q: Polynomial) -> Polynomial:
        result: Polynomial = defaultdict(Fraction)
        for (a, b), c in p.items():
            for (d, e0), f in q.items():
                result[(a+d, b+e0)] += c*f
        return clean(result)

    def project(p: Polynomial) -> Polynomial:
        return {e0: value for e0, value in p.items() if e0[1] == 0}

    rng = random.Random(20260923)
    for test in range(100):
        c: Polynomial = {}
        x: Polynomial = {}
        for _ in range(12):
            c[(rng.randrange(-8, 9), 0)] = Fraction(rng.randrange(-5, 6),
                                                   rng.randrange(1, 8))
            x[(rng.randrange(-8, 9), rng.randrange(-4, 5))] = Fraction(
                rng.randrange(-5, 6), rng.randrange(1, 8))
        c, x = clean(c), clean(x)
        checks.check("finite support projection", f"linearity instance {test}",
                     project(multiply(c, x)) == multiply(c, project(x)))
    checks.check("finite support projection", "not a multiplicative projection",
                 project(multiply({(0, 1): Fraction(1)}, {(0, -1): Fraction(1)}))
                 != multiply(project({(0, 1): Fraction(1)}),
                             project({(0, -1): Fraction(1)})))

    a, b, c, d, x, y = sp.symbols("a b c d x y")
    imaginary = sp.I
    first, second = a+b*imaginary, a-b*imaginary
    checks.check("Gaussian splitting", "inverse constant coefficient",
                 sp.expand((first+second)/2-a) == 0)
    checks.check("Gaussian splitting", "inverse imaginary coefficient",
                 sp.expand((first-second)/(2*imaginary)-b) == 0)
    for sign in (1, -1):
        product = (a+sign*b*imaginary)*(c+sign*d*imaginary)
        image_product = (a*c-b*d)+sign*(a*d+b*c)*imaginary
        checks.check("Gaussian splitting", f"multiplicativity {sign}",
                     sp.expand(product-image_product) == 0)
    for sign in (1, -1):
        recovered = (x+y)/2 + sign*((x-y)/(2*imaginary))*imaginary
        checks.check("Gaussian splitting", f"surjectivity {sign}",
                     sp.expand(recovered-(x if sign == 1 else y)) == 0)

    # Splitting C tensor_Q Q(sqrt(2),sqrt(3)): rows are the four embeddings.
    signs = tuple(itertools.product((-1, 1), repeat=2))
    matrix = sp.Matrix([[1, a0*sp.sqrt(2), b0*sp.sqrt(3), a0*b0*sp.sqrt(6)]
                        for a0, b0 in signs])
    checks.check("finite Galois splitting", "four embeddings are independent",
                 sp.simplify(matrix.det()) != 0)
    inverse = matrix.inv()
    identity = (matrix*inverse).applyfunc(sp.simplify)
    for row in range(4):
        for col in range(4):
            checks.check("finite Galois splitting", f"splitting matrix {row},{col}",
                         identity[row, col] == int(row == col))
    for a0, b0 in signs:
        for a1, b1 in signs:
            # Evaluation of the primitive projector
            # (1+a0*sqrt(2)/sqrt(2))*(1+b0*sqrt(3)/sqrt(3))/4.
            value = Fraction((1+a0*a1)*(1+b0*b1), 4)
            checks.check("finite Galois splitting", f"Galois atom {a0,b0},{a1,b1}",
                         value == int((a0, b0) == (a1, b1)))

    return {
        "status": "passed",
        "sympy_version": sp.__version__,
        "total_assertions": sum(checks.counts.values()),
        "groups": dict(checks.counts),
        "Boolean_variables_tested": [1, 2, 3, 4, 5, 6],
        "Boolean_assignments_tested": atom_rows,
        "Laurent_coefficients_in_z_equals_T_inverse":
            {str(k): str(v) for k, v in expected.items()},
        "finite_Galois_splitting_determinant": str(sp.simplify(matrix.det())),
        "limits": [
            "No formal verification of the main theorem is performed.",
            "Finite support tests do not prove arbitrary Hahn-support statements.",
            "Boolean truth tables do not prove survival of localization denominators.",
            "No transfinite construction, prime-ideal existence, or cardinality is computed.",
            "No claim of historical priority follows from these tests."
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Write JSON results to this path as well as standard output.")
    args = parser.parse_args()
    report = run_checks()
    text = json.dumps(report, indent=2, ensure_ascii=True)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
