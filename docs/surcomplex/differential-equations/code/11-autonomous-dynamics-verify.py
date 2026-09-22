#!/usr/bin/env python3
"""Exact finite checks for article.tex; these are not a proof assistant.

Requires Python 3.10+ and SymPy. No network access, floating-point arithmetic,
or numerical claims about surreal limits are used. All series computations
are in a finite total-degree quotient of Q[C][X,Y].
"""
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

X, Y, C = sp.symbols("X Y C")


@dataclass(frozen=True)
class TruncatedRing:
    """Bivariate polynomials modulo terms of total degree > cutoff."""
    cutoff: int

    def cut(self, expr: sp.Expr) -> sp.Expr:
        poly = sp.Poly(sp.expand(expr), X, Y)
        return sp.Add(*(coeff * X**i * Y**j
                        for (i, j), coeff in poly.terms()
                        if i + j <= self.cutoff))

    def mul(self, a: sp.Expr, b: sp.Expr) -> sp.Expr:
        return self.cut(a * b)

    def inverse_unit(self, f: sp.Expr) -> sp.Expr:
        if sp.expand(f).subs({X: 0, Y: 0}) != 1:
            raise ValueError("inverse_unit requires constant term one")
        u, power, out = self.cut(f - 1), sp.Integer(1), sp.Integer(1)
        for k in range(1, self.cutoff + 1):
            power = self.mul(power, u)
            out += (-1)**k * power
        return self.cut(out)

    def log_unit(self, f: sp.Expr) -> sp.Expr:
        if sp.expand(f).subs({X: 0, Y: 0}) != 1:
            raise ValueError("log_unit requires constant term one")
        u, power, out = self.cut(f - 1), sp.Integer(1), sp.Integer(0)
        for k in range(1, self.cutoff + 1):
            power = self.mul(power, u)
            out += sp.Rational((-1)**(k + 1), k) * power
        return self.cut(out)

    def equation(self, f: sp.Expr) -> sp.Expr:
        # Equation (exampleimplicit) in article.tex.
        return self.cut(self.inverse_unit(f)
                        + X * self.log_unit(f) - Y
                        - X * self.log_unit(1 + X * f)
                        - C * X - 1)

    def homogeneous(self, f: sp.Expr, degree: int) -> sp.Expr:
        return sp.Add(*(a * X**i * Y**j
                        for (i, j), a in sp.Poly(sp.expand(f), X, Y).terms()
                        if i + j == degree))


def check_zero(name: str, expr: sp.Expr) -> None:
    result = sp.simplify(expr)
    if result != 0:
        raise AssertionError(f"{name}: expected zero, received {result}")
    print(f"PASS: {name}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, default=4,
                        help="total-degree truncation order (2 to 7; default 4)")
    args = parser.parse_args()
    if not 2 <= args.degree <= 7:
        parser.error("--degree must be between 2 and 7")

    print("EXACT VERIFICATION RECORD")
    print(f"Python: {sys.version.split()[0]}; SymPy: {sp.__version__}")
    print("No numerical approximation or fine-topological convergence is asserted.\n")

    q, c, w, t = sp.symbols("q c w t")
    logistic = c * q / (1 + c * q)
    check_zero("logistic equation with Dq = -q",
               -q * sp.diff(logistic, q) + logistic - logistic**2)

    repeated = 4 / (w + C)**2
    check_zero("repeated-root counterexample: (Dy)^2 = y^3",
               sp.diff(repeated, w)**2 - repeated**3)

    cosh = (q + 1 / q) / 2
    check_zero("degree-two counterexample with Dq = q",
               (q * sp.diff(cosh, q))**2 - cosh**2 + 1)

    time_primitive = 1 / t + sp.log(t) - sp.log(1 + t)
    check_zero("local time primitive for f(t) = -t^2(1+t)",
               sp.diff(time_primitive, t) * (-t**2 * (1 + t)) - 1)

    n = args.degree
    ring = TruncatedRing(n)
    f = sp.Integer(1)
    pieces: list[sp.Expr] = []
    for d in range(1, n + 1):
        residual = ring.homogeneous(ring.equation(f), d)
        # Constant derivative of the implicit equation with respect to F is -1.
        correction = residual
        f = ring.cut(f + correction)
        pieces.append(correction)
        check_zero(f"implicit equation through total degree {d}",
                   TruncatedRing(d).equation(f))

    a = Y + C * X
    expected2 = 1 - a + a**2 - X * a - X**2
    check_zero("printed first two homogeneous corrections",
               TruncatedRing(2).cut(f - expected2))

    print("\nComputed homogeneous corrections:")
    for d, piece in enumerate(pieces, start=1):
        print(f"F_{d} = {sp.factor(piece)}")

    # After X=1/w and Y=X*L, where L=log(w), D=-X^2 d/dX + X d/dL.
    # A total-degree N truncation of F gives a parameter u correct through
    # X^(N+1), and its differential residual has no terms through X^(N+2).
    L = sp.symbols("L")
    u = sp.expand(X * f.subs(Y, X * L))
    Du = sp.expand(-X**2 * sp.diff(u, X) + X * sp.diff(u, L))
    residual = sp.Poly(sp.expand(Du + u**2 * (1 + u)), X)
    low = sp.Add(*(coeff * X**k for (k,), coeff in residual.terms()
                   if k <= n + 2))
    check_zero(f"differential residual through X^{n+2}, with L = log(w)", low)
    nonzero_degrees = [k for (k,), coeff in residual.terms() if coeff != 0]
    first = min(nonzero_degrees) if nonzero_degrees else None
    print(f"First possibly nonzero degree of the finite-truncation residual: {first}")
    print("\nAll requested exact finite checks passed.")
    print("These tests do not verify the general proofs, formalization, or novelty.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
