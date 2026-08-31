#!/usr/bin/env python3
"""Exact symbolic checks for the q-Fabius frontier report.

The script uses SymPy rational arithmetic to verify the identities quoted in
q_fabius_parameter_frontiers.tex.  It is intentionally separate from experiments.py:
this file checks algebra exactly, while experiments.py studies numerical error
laws and produces figures.
"""

from __future__ import annotations

from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data"
DATA.mkdir(exist_ok=True)

q, delta, theta, x, z = sp.symbols("q delta theta x z")


def uniform_cumulant(order: int) -> sp.Expr:
    """Classical cumulant of Uniform[-1,1] in exact Bernoulli form."""
    if order % 2 or order < 2:
        return sp.Integer(0)
    m = order // 2
    return sp.Rational(2) ** (2 * m - 1) * sp.bernoulli(2 * m) / m


def geometric_cumulant(order: int) -> sp.Expr:
    """Cumulant of X_q=(1-q) sum q^j U_j."""
    return sp.factor(uniform_cumulant(order) * (1 - q) ** order / (1 - q**order))


def standardized_cumulant(m: int) -> sp.Expr:
    """Standardized cumulant lambda_{2m}(q)."""
    variance = geometric_cumulant(2)
    return sp.factor(geometric_cumulant(2 * m) / variance**m)


def rate_series(max_m: int = 8) -> tuple[sp.Expr, sp.Expr]:
    """Return theta(x) and I(x) through x^(2*max_m), exactly.

    Since I'(x)=theta(x), series reversion of x=Lambda'(theta) is enough.
    The coefficients are solved one at a time; each new coefficient enters
    linearly because Lambda''(0)=1/6 is nonzero.
    """
    xp = sp.Integer(0)
    for m in range(1, max_m + 1):
        xp += uniform_cumulant(2 * m) * theta ** (2 * m - 1) / sp.factorial(2 * m)

    unknowns = sp.symbols("b1:" + str(max_m + 1))
    inverse = sp.Integer(0)
    solved: dict[sp.Symbol, sp.Expr] = {}
    for m, b in enumerate(unknowns, start=1):
        inverse += b * x ** (2 * m - 1)
        composed = sp.series(xp.subs(theta, inverse).subs(solved), x, 0, 2 * m + 1).removeO()
        equation = sp.expand(composed - x).coeff(x, 2 * m - 1)
        solved[b] = sp.solve(sp.Eq(equation, 0), b)[0]
    inverse = sp.expand(inverse.subs(solved))
    rate = sp.integrate(inverse, (x, 0, x))
    return inverse, sp.expand(rate)


def main() -> None:
    lines: list[str] = []
    lines.append("Exact symbolic checks for the q-Fabius frontier report")
    lines.append("=" * 60)
    lines.append("")
    lines.append("Classical cumulants of X_q:")
    for m in range(1, 7):
        lines.append(f"kappa_{2*m} = {sp.sstr(geometric_cumulant(2*m))}")

    lines.append("")
    lines.append("Standardized cumulants and delta=-log(q) expansions:")
    for m in range(2, 7):
        lam = standardized_cumulant(m)
        hyperbolic = sp.factor(sp.simplify(lam.subs(q, sp.exp(-delta))))
        expansion = sp.series(hyperbolic, delta, 0, 7)
        lines.append(f"lambda_{2*m}(q) = {sp.sstr(lam)}")
        lines.append(f"lambda_{2*m}(e^-delta) = {sp.sstr(hyperbolic)}")
        lines.append(f"series = {sp.sstr(expansion)}")

    # Exact coefficient kernel and cocycle.
    r, s, t = sp.symbols("r s t")
    A = lambda a: (1 - a) / (1 - a * z)
    P = lambda a, b: sp.factor(A(b) / A(a))
    lines.append("")
    lines.append("Parameter-flow generating functions:")
    lines.append(f"P_rs(z) = {sp.sstr(P(r,s))}")
    lines.append(f"cocycle residual = {sp.sstr(sp.factor(P(r,t)-P(r,s)*P(s,t)))}")

    # Center rate series.
    inverse, rate = rate_series(max_m=8)
    lines.append("")
    lines.append("Inverse saddle series theta(x):")
    lines.append(sp.sstr(inverse))
    lines.append("Rate series I(x):")
    lines.append(sp.sstr(rate))
    coeff_signs = [sp.sign(rate.coeff(x, 2 * m)) for m in range(1, 9)]
    lines.append(f"signs through x^16 = {coeff_signs}")

    # First Edgeworth polynomials in the natural delta scale.
    H = lambda n: sp.hermite_prob(n, x)
    Q1 = -H(4) / 20
    Q2 = sp.Rational(4, 315) * H(6) + H(8) / 800
    Q3 = H(4) / 60 - sp.Rational(3, 700) * H(8) - H(10) / 1575 - H(12) / 48000
    lines.append("")
    lines.append("Edgeworth polynomials in delta=-log(q):")
    lines.append(f"Q1 = {sp.sstr(sp.expand(Q1))}")
    lines.append(f"Q2 = {sp.sstr(sp.expand(Q2))}")
    lines.append(f"Q3 = {sp.sstr(sp.expand(Q3))}")

    # Midpoint Euler--Maclaurin first two coefficient operators.
    g = sp.log(sp.sinh(theta) / theta)
    D = lambda f: sp.simplify(theta * sp.diff(f, theta))
    c2 = sp.simplify((g - D(g)) / 24)
    c4 = sp.simplify((7 * D(D(D(g))) - 10 * D(D(g)) + 5 * D(g) - 2 * g) / 5760)
    lines.append("")
    lines.append("Midpoint Euler--Maclaurin coefficients:")
    lines.append(f"C2(theta) = {sp.sstr(c2)}")
    lines.append(f"C4(theta) = {sp.sstr(c4)}")
    lambda_second = sp.simplify(sp.diff(g / theta, theta))
    lines.append(f"C2 + theta^2 Lambda''/24 = {sp.sstr(sp.simplify(c2 + theta**2*lambda_second/24))}")

    output = "\n".join(lines) + "\n"
    (DATA / "symbolic_checks.txt").write_text(output)
    print(output)


if __name__ == "__main__":
    main()
