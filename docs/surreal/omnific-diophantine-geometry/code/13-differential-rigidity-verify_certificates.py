#!/usr/bin/env python3
"""Exact finite checks accompanying Differential Rigidity of Omnific Points.

Requires Python 3.10+ and SymPy. No network access is used. These checks verify
finite algebraic certificates, not the general Hahn/scheme-theoretic proofs.
Run: python verify_certificates.py --output verification_report.txt
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import random
import sys
from typing import Callable, Mapping

try:
    import sympy as sp
except ImportError as exc:
    raise SystemExit("SymPy is required: install it in your Python environment.") from exc

Exponent = tuple[Fraction, Fraction]
ZERO: Exponent = (Fraction(0), Fraction(0))


def add_exp(a: Exponent, b: Exponent) -> Exponent:
    return (a[0] + b[0], a[1] + b[1])


@dataclass(frozen=True)
class FiniteHahn:
    """Finite rational-coefficient Hahn sums, lexicographic exponent group Q^2."""
    terms: Mapping[Exponent, Fraction]

    def __post_init__(self) -> None:
        clean: dict[Exponent, Fraction] = {}
        for exponent, coefficient in self.terms.items():
            if len(exponent) != 2:
                raise ValueError("Expected two exponent coordinates.")
            e = (Fraction(exponent[0]), Fraction(exponent[1]))
            c = Fraction(coefficient)
            if c:
                clean[e] = clean.get(e, Fraction(0)) + c
        object.__setattr__(self, "terms", {e: c for e, c in clean.items() if c})

    def __add__(self, other: FiniteHahn) -> FiniteHahn:
        result = dict(self.terms)
        for e, c in other.terms.items():
            result[e] = result.get(e, Fraction(0)) + c
        return FiniteHahn(result)

    def __mul__(self, other: FiniteHahn) -> FiniteHahn:
        result: dict[Exponent, Fraction] = {}
        for e, a in self.terms.items():
            for f, b in other.terms.items():
                ef = add_exp(e, f)
                result[ef] = result.get(ef, Fraction(0)) + a * b
        return FiniteHahn(result)

    def derivative(self, lam: Callable[[Exponent], Fraction]) -> FiniteHahn:
        return FiniteHahn({e: c * lam(e) for e, c in self.terms.items()})

    def degree(self) -> Exponent:
        if not self.terms:
            raise ValueError("The zero series has no finite degree.")
        return max(self.terms)

    def constant(self) -> Fraction:
        return self.terms.get(ZERO, Fraction(0))

    def in_B(self) -> bool:
        return all(e >= ZERO for e in self.terms)

    def in_I(self) -> bool:
        return all(e > ZERO for e in self.terms)

    def in_O(self) -> bool:
        return all(e <= ZERO for e in self.terms)

    def in_m(self) -> bool:
        return all(e < ZERO for e in self.terms)


def squarefree_certificate(F: sp.Expr, x: sp.Symbol, m: int) -> tuple[sp.Expr, sp.Expr]:
    """Return U,V in Q[X] with U F + V F' = 1 after validating assumptions."""
    if not isinstance(m, int) or m < 2:
        raise ValueError("m must be an ordinary integer at least two.")
    polynomial = sp.Poly(F, x, domain=sp.QQ)
    if polynomial.degree() < 2:
        raise ValueError("The polynomial degree must be at least two.")
    if sp.gcd(polynomial, polynomial.diff()).degree() != 0:
        raise ValueError("The polynomial must be squarefree.")
    U, V, g = sp.gcdex(polynomial, polynomial.diff())
    if g.is_zero:
        raise ArithmeticError("Unexpected zero gcd.")
    scale = g.as_expr()
    return sp.cancel(U.as_expr() / scale), sp.cancel(V.as_expr() / scale)


def run_checks() -> list[str]:
    counts: dict[str, int] = {}

    def check(category: str, condition: bool, detail: str) -> None:
        if not bool(condition):
            raise AssertionError(f"{category}: {detail}")
        counts[category] = counts.get(category, 0) + 1

    x, y, a, b, dx, dy = sp.symbols("x y a b dx dy")
    F = x**3 + a*x + b
    delta = 4*a**3 + 27*b**2
    U = -9*(2*a*x - 3*b)/delta
    V = (4*a**2 + 6*a*x**2 - 9*b*x)/delta
    check("universal cubic certificate", sp.cancel(U*F + V*sp.diff(F, x) - 1) == 0,
          "U F + V F' must equal one")
    h = U*y*dx/2 + V*dy
    certificate = U*(y**2-F)*dx + V*(2*y*dy-sp.diff(F, x)*dx)
    check("universal cubic certificate", sp.cancel(2*y*h-dx-certificate) == 0,
          "the cleared differential identity must hold")

    a1, a2, a3, a4, a6 = sp.symbols("a1 a2 a3 a4 a6")
    original = y*y+a1*x*y+a3*y-(x**3+a2*x*x+a4*x+a6)
    Q = 4*x**3+(a1*a1+4*a2)*x*x+(2*a1*a3+4*a4)*x+(a3*a3+4*a6)
    check("Weierstrass transformation", sp.expand((2*y+a1*x+a3)**2-Q-4*original) == 0,
          "completion of the square")

    polynomials: list[sp.Expr] = [x**d+x+1 for d in range(2, 10)]
    polynomials += [x**3-x+1, x**3+2*x+3, x*(x-1)*(x+1),
                    x**5-x+1, (x-2)*(x+3)*(x*x+1), x*x-1]
    for P in polynomials:
        for m in range(2, 9):
            u, v = squarefree_certificate(P, x, m)
            check("squarefree Bezout identities", sp.expand(u*P+v*sp.diff(P, x)-1) == 0,
                  f"polynomial {P}, m={m}")
            H = u*y*dx/m+v*dy
            rhs = u*(y**m-P)*dx+v*(m*y**(m-1)*dy-sp.diff(P, x)*dx)
            check("cleared differential identities",
                  sp.expand(m*y**(m-1)*H-dx-rhs) == 0, f"polynomial {P}, m={m}")
    for P, m in [(x**3, 2), ((x-1)**2*(x+2), 3), (x+1, 2), (x*x+1, 1)]:
        rejected = False
        try:
            squarefree_certificate(P, x, m)
        except ValueError:
            rejected = True
        check("assumption rejection", rejected, f"invalid input {P}, m={m}")

    equality_cases = []
    for m in range(2, 101):
        for d in range(2, 101):
            coefficient = m-(m-1)*d
            check("degree coefficient inequalities", coefficient <= 0, f"m={m}, d={d}")
            if coefficient == 0:
                equality_cases.append((m, d))
    check("degree equality case", equality_cases == [(2, 2)], "unique endpoint")

    rng = random.Random(20260923)
    def random_series(region: str) -> FiniteHahn:
        result: dict[Exponent, Fraction] = {}
        for _ in range(rng.randrange(2, 12)):
            e = (Fraction(rng.randint(-6, 6), rng.randint(1, 5)),
                 Fraction(rng.randint(-6, 6), rng.randint(1, 5)))
            if region == "B" and e < ZERO or region == "O" and e > ZERO:
                e = (-e[0], -e[1])
            result[e] = result.get(e, Fraction(0)) + Fraction(rng.randint(-5, 5), rng.randint(1, 5))
        return FiniteHahn(result)

    for _ in range(160):
        l0, l1 = Fraction(rng.randint(-4, 4)), Fraction(rng.randint(-4, 4))
        lam = lambda e, p=l0, q=l1: p*e[0]+q*e[1]
        for region in ["K", "B", "O"]:
            f, g = random_series(region), random_series(region)
            df, dg = f.derivative(lam), g.derivative(lam)
            check("finite Hahn Leibniz", (f*g).derivative(lam) == df*g+f*dg, region)
            check("support containment", set(df.terms) <= set(f.terms), region)
            if f.terms and g.terms:
                check("degree multiplicativity", (f*g).degree() == add_exp(f.degree(), g.degree()), region)
            if df.terms:
                check("derivative degree bound", df.degree() <= f.degree(), region)
            if region == "B":
                check("two-ring inclusions", df.in_I(), "D B subset I")
                check("constant retraction", (f*g).constant() == f.constant()*g.constant(), "ct product")
            if region == "O":
                check("two-ring inclusions", df.in_m(), "D O subset m")
            killed_both = not f.derivative(lambda e: e[0]).terms and not f.derivative(lambda e: e[1]).terms
            check("family detects constants", killed_both == (set(f.terms) <= {ZERO}), region)

    # A single character need not have only scalar constants.
    f = FiniteHahn({(Fraction(0), Fraction(1)): Fraction(1)})
    check("single derivation caution", not f.derivative(lambda e: e[0]).terms,
          "a nonconstant may be killed by one character")
    check("single derivation caution", bool(f.derivative(lambda e: e[1]).terms),
          "another character detects it")

    t = sp.symbols("t")
    check("sharpness identities", sp.expand((t**3)**2-(t**2)**3) == 0, "singular cusp")
    check("sharpness identities", sp.expand((t*t-1)**2+(2*t)**2-(t*t+1)**2) == 0,
          "projective conic")
    check("sharpness identities", sp.expand(t/2*(2*t)-(t*t-1)) == 1,
          "omnific unimodularity witness")
    # Polynomial isomorphism of an affine line model, with a fiber over (2,5).
    X, Y = 2+t, 5+3*t+t*t
    check("affine-line fiber identities", sp.expand(Y-(X*X-X+3)) == 0, "polynomial lift")
    check("affine-line fiber identities", (X.subs(t, 0), Y.subs(t, 0)) == (2, 5), "base point")

    lines = ["EXACT FINITE CERTIFICATE REPORT", "="*31,
             f"Python: {sys.version.split()[0]}", f"SymPy: {sp.__version__}",
             "Random seed: 20260923", ""]
    for category, count in counts.items():
        lines.append(f"PASS  {category}: {count}")
    lines += ["", f"TOTAL: {sum(counts.values())} exact assertions passed.", "",
              "Scope: finite symbolic algebra and finite Hahn sums only.",
              "Not checked by this script: arbitrary infinite Hahn supports;",
              "properness; Kahler-differential sheaf arguments; Riemann-Roch;",
              "algebraic-group structure; formal proof correctness or novelty.",
              "Those mathematical arguments are supplied in the article."]
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Optional report destination.")
    args = parser.parse_args()
    text = "\n".join(run_checks())+"\n"
    print(text, end="")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
