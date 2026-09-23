#!/usr/bin/env python3
"""Exact finite checks for 'Omnific Points of Algebraic Groups'.

Requires SymPy. These checks do not implement surreal numbers, infinite Hahn
summation, algebraic-group classification, or proper-class homomorphisms.
Run: python verification.py --output verification-results.txt
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import permutations
from pathlib import Path
import platform
import random
import sys

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

COUNTS: Counter[str] = Counter()


def matrix_equal(left: sp.MatrixBase, right: sp.MatrixBase, category: str) -> None:
    """Check every entry exactly, counting one complete matrix identity."""
    if left.shape != right.shape:
        raise AssertionError(f"Shape mismatch in {category}: {left.shape} != {right.shape}")
    residual = (left - right).applyfunc(sp.expand)
    if any(sp.simplify(entry) != 0 for entry in residual):
        raise AssertionError(f"Identity failed in {category}: {residual}")
    COUNTS[category] += 1


def scalar_equal(left: sp.Expr, right: sp.Expr, category: str) -> None:
    if sp.simplify(sp.expand(left - right)) != 0:
        raise AssertionError(f"Identity failed in {category}: {left} != {right}")
    COUNTS[category] += 1


def elementary(n: int, i: int, j: int, a: sp.Expr | int) -> sp.Matrix:
    if n < 2 or not 0 <= i < n or not 0 <= j < n or i == j:
        raise ValueError("An elementary matrix needs valid distinct row and column indices.")
    out = sp.eye(n)
    out[i, j] = a
    return out


def root_checks() -> None:
    a, b, c, r = sp.symbols("a b c r", commutative=True)
    for n in range(3, 7):
        for i, j in permutations(range(n), 2):
            matrix_equal(elementary(n, i, j, a) * elementary(n, i, j, b),
                         elementary(n, i, j, a+b), "root addition")
        for i, h, j in permutations(range(n), 3):
            x, xi = elementary(n, i, h, b), elementary(n, i, h, -b)
            y, yi = elementary(n, h, j, c), elementary(n, h, j, -c)
            z, zi = elementary(n, j, i, r), elementary(n, j, i, -r)
            cx = elementary(n, j, h, r*b) * x
            cy = elementary(n, h, i, -c*r) * y
            cxi = xi * elementary(n, j, h, -r*b)
            cyi = yi * elementary(n, h, i, c*r)
            matrix_equal(x*y*xi*yi, elementary(n, i, j, b*c), "third-index commutator")
            matrix_equal(z*x*zi, cx, "opposite-root conjugation, first factor")
            matrix_equal(z*y*zi, cy, "opposite-root conjugation, second factor")
            matrix_equal(z*elementary(n, i, j, b*c)*zi, cx*cy*cxi*cyi,
                         "opposite-root normality identity")


def orthogonal_checks() -> None:
    s, t = sp.symbols("s t", commutative=True)
    examples = [
        ("real rationally anisotropic example", sp.diag(1, 1, -3),
         sp.Matrix([sp.sqrt(3), 0, 1]), sp.Matrix([0, 1, 0]), (2, 1)),
        ("complex compact-form escape", sp.eye(3),
         sp.Matrix([1, sp.I, 0]), sp.Matrix([0, 0, 1]), (0, 2)),
    ]
    for name, q, v, w, recovery in examples:
        n = v*w.T*q - w*v.T*q
        def g(a: sp.Expr) -> sp.Matrix:
            return sp.eye(3) + a*n + a*a*n*n/2
        matrix_equal(n**3, sp.zeros(3), name)
        if n**2 == sp.zeros(3):
            raise AssertionError(f"Unexpected nilpotence degree in {name}")
        COUNTS[name] += 1
        matrix_equal(n.T*q+q*n, sp.zeros(3), name)
        matrix_equal(g(s).T*q*g(s), q, name)
        scalar_equal(g(s).det(), sp.Integer(1), name)
        matrix_equal(g(s)*g(t), g(s+t), name)
        matrix_equal(g(s)*g(-s), sp.eye(3), name)
        u = g(s)-sp.eye(3)
        matrix_equal(u-u*u/2, s*n, name)
        scalar_equal(g(s)[recovery], s, name)


def filtration_checks() -> None:
    rng = random.Random(20260923)
    for n in range(3, 9):
        for r in range(1, n):
            for s in range(1, n):
                x, y = sp.zeros(n), sp.zeros(n)
                for i in range(n):
                    for j in range(i+1, n):
                        if j-i >= r:
                            x[i, j] = rng.randrange(-2, 3)
                        if j-i >= s:
                            y[i, j] = rng.randrange(-2, 3)
                def inverse_unit(u: sp.Matrix) -> sp.Matrix:
                    result, power = sp.eye(n), sp.eye(n)
                    for _ in range(1, n):
                        power = power * (-u)
                        result += power
                    return result
                comm = (sp.eye(n)+x)*(sp.eye(n)+y)*inverse_unit(x)*inverse_unit(y)
                for i in range(n):
                    for j in range(n):
                        if i == j and comm[i, j] != 1:
                            raise AssertionError("Nonunit diagonal in filtration check")
                        if (i > j or 0 < j-i < r+s) and comm[i, j] != 0:
                            raise AssertionError("Wrong commutator filtration")
                COUNTS["unitriangular filtration (exact integer instances)"] += 1


def support_identity_checks() -> None:
    z, c = sp.symbols("z c", commutative=True)
    for m in range(13):
        scalar_equal(c*(1-z)*sum(z**j for j in range(m+1)),
                     c*(1-z**(m+1)), "finite geometric remainder")
    rng = random.Random(240923)
    for _ in range(30):
        def series() -> dict[Fraction, sp.Expr]:
            out: dict[Fraction, sp.Expr] = {}
            for _ in range(8):
                e = Fraction(rng.randrange(0, 16), rng.randrange(1, 5))
                out[e] = out.get(e, sp.Integer(0)) + rng.randrange(-4, 5)
            return out
        a, b = series(), series()
        product: dict[Fraction, sp.Expr] = {}
        for e, u in a.items():
            for f, v in b.items():
                product[e+f] = product.get(e+f, sp.Integer(0)) + u*v
        scalar_equal(sum(product.values(), sp.Integer(0)),
                     sum(a.values(), sp.Integer(0))*sum(b.values(), sp.Integer(0)),
                     "finite-support augmentation")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the finite-check report to this path")
    args = parser.parse_args()
    root_checks()
    orthogonal_checks()
    filtration_checks()
    support_identity_checks()
    lines = ["OMNIFIC GROUPS: EXACT FINITE VERIFICATION", "",
             f"Python {platform.python_version()}; SymPy {sp.__version__}",
             "Commutator convention: [x,y] = x*y*x^(-1)*y^(-1).", ""]
    lines += [f"PASS  {name}: {count}" for name, count in COUNTS.items()]
    lines += ["", f"TOTAL: {sum(COUNTS.values())} exact checks passed.", "",
              "Scope: symbolic polynomial matrix identities, finite geometric remainders,",
              "finite-support augmentation, and deterministic integer filtration instances.",
              "NOT CHECKED: infinite Hahn summability, surreal support gaps, proper-class",
              "cardinal arguments, algebraic-group structure, or all claims of the article.",
              "No Lean verification or numerical approximation is claimed."]
    report = "\n".join(lines) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(report, encoding="utf-8")
    print(report, end="")
    return 0


if __name__ == "__main__":
    sys.exit(main())
