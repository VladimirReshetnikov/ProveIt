#!/usr/bin/env python3
"""Exact finite algebra checks for Transfinite Critical Potentials over the Surreals.

Run with Python 3.10+ and SymPy:
    python verify.py
    python verify.py --output verification.txt

These tests do NOT construct surreal numbers, prove transfinite summability,
verify the cited log-atomic derivative theorem, or establish novelty. The
infinite and field-membership arguments are in article.tex / article.pdf.
No network access, floating-point arithmetic, or external services are used.
"""
from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import sys
from typing import Callable

try:
    import sympy as sp
except ImportError:
    sys.exit("SymPy is required. Install it with: python -m pip install sympy")


class Checks:
    """Collect named exact identities, raising an exception on any failure."""

    def __init__(self) -> None:
        self.rows: list[tuple[str, str]] = []

    def zero(self, suite: str, name: str, expression: sp.Expr) -> None:
        residual = sp.simplify(sp.expand(expression))
        if residual != 0:
            raise AssertionError(f"{suite}: {name}\nNonzero residual: {residual}")
        self.rows.append((suite, name))


def jet_derivation(rules: dict[sp.Symbol, sp.Expr]) -> Callable[[sp.Expr], sp.Expr]:
    """Derivation of a finite rational/polynomial algebra from generator images."""
    def derive(expression: sp.Expr) -> sp.Expr:
        expression = sp.sympify(expression)
        return sp.expand(sum(sp.diff(expression, x) * dx for x, dx in rules.items()))
    return derive


def critical_hierarchy(checks: Checks) -> None:
    r, c = sp.symbols("r c")
    for n in range(13):
        aa = sp.symbols(f"a0:{n+1}")
        rules = {a: -a * sum(aa[: j + 1]) for j, a in enumerate(aa)}
        derive = jet_derivation(rules)
        A = sp.sympify(sum(aa[:n]))
        squares = sp.sympify(sum(a**2 for a in aa[:n]))
        h = A / 2
        Q = squares / 4
        checks.zero("Finite hierarchy", f"triangular identity at length {n}",
                    derive(A) + (A**2 + squares) / 2)
        checks.zero("Finite hierarchy", f"critical potential at length {n}",
                    derive(h) + h**2 + Q)
        b = h + r * aa[n]
        checks.zero("Finite hierarchy", f"Riccati residual at length {n}",
                    derive(b) + b**2 + Q + c * aa[n]**2
                    - (r**2 - r + c) * aa[n]**2)


def euler_equation(checks: Checks) -> None:
    T = sp.Symbol("T", positive=True)
    r, d, c = sp.symbols("r d c", real=True)
    E = lambda f: T * sp.diff(f, T)
    checks.zero("Euler equation", "arbitrary real power eigenvalue", E(T**r) - r*T**r)
    checks.zero("Euler equation", "Euler polynomial residual",
                E(E(T**r)) - E(T**r) + c*T**r - (r**2-r+c)*T**r)
    roots = (sp.Rational(1, 2) + d, sp.Rational(1, 2) - d)
    for index, rr in enumerate(roots):
        y = T**rr
        checks.zero("Euler equation", f"distinct-root basis element {index+1}",
                    sp.diff(y, T, 2) + (sp.Rational(1, 4)-d**2)*y/T**2)
    y1, y2 = (T**rr for rr in roots)
    checks.zero("Euler equation", "distinct-root Wronskian equals -2d",
                y1*sp.diff(y2, T)-sp.diff(y1,T)*y2+2*d)
    y1, y2 = sp.sqrt(T), sp.sqrt(T)*sp.log(T)
    for index, y in enumerate((y1, y2)):
        checks.zero("Euler equation", f"repeated-root basis element {index+1}",
                    sp.diff(y,T,2) + y/(4*T**2))
    checks.zero("Euler equation", "repeated-root Wronskian equals one",
                y1*sp.diff(y2,T)-sp.diff(y1,T)*y2-1)


def liouville_gauge(checks: Checks) -> None:
    U, Up, Upp, T, Tp, Tpp, v, vT, vTT, Q, c = sp.symbols(
        "U Up Upp T Tp Tpp v vT vTT Q c", nonzero=True)
    relations = {Tp: U**-2, Tpp: -2*Up/U**3, Upp: -Q*U}
    checks.zero("Gauge identity", "normalization U^2 T' = 1",
                (U**2*Tp-1).subs(relations))
    checks.zero("Gauge identity", "first-derivative cancellation",
                (2*Up*Tp+U*Tpp).subs(relations))
    lhs = (Upp+Q*U)*v+(2*Up*Tp+U*Tpp)*vT+U*Tp**2*vTT+c*(Tp/T)**2*U*v
    rhs = U*Tp**2/T**2*(T**2*vTT+c*v)
    checks.zero("Gauge identity", "full conjugated differential operator",
                (lhs-rhs).subs(relations))
    checks.zero("Gauge identity", "Wronskian of (U,UT)",
                (U*(Up*T+U*Tp)-Up*(U*T)-1).subs(relations))


def schwarzian(checks: Checks) -> None:
    t, p, q, r = sp.symbols("t p q r", positive=True)
    derive = jet_derivation({t:p, p:q, q:r})
    w = p**(-sp.Rational(1,2))
    S = r/p-sp.Rational(3,2)*(q/p)**2
    checks.zero("Schwarzian", "normalized square root identity", derive(derive(w))/w+S/2)
    checks.zero("Schwarzian", "normalized pair Wronskian", w*derive(w*t)-derive(w)*w*t-1)
    checks.zero("Schwarzian", "second solution from normalized coordinate",
                derive(derive(w*t))+(S/2)*w*t)

    u, du, v, dv, Q, dQ = sp.symbols("u du v dv Q dQ")
    derive = jet_derivation({u:du, du:-Q*u, v:dv, dv:-Q*v, Q:dQ})
    t = v/u
    dt = sp.factor(derive(t))
    ddt = sp.factor(derive(dt))
    dddt = sp.factor(derive(ddt))
    checks.zero("Schwarzian", "ratio of two solutions has Schwarzian 2Q",
                dddt/dt-sp.Rational(3,2)*(ddt/dt)**2-2*Q)


def picard_vessiot(checks: Checks) -> None:
    U, T, h, Q, a, b, c, d = sp.symbols("U T h Q a b c d", nonzero=True)
    derive = jet_derivation({U:h*U, T:U**-2, h:-Q-h**2})
    Phi = sp.Matrix([[U,U*T],[h*U,h*U*T+U**-1]])
    companion = sp.Matrix([[0,1],[-Q,0]])
    checks.zero("Picard-Vessiot", "fundamental determinant", Phi.det()-1)
    residual = Phi.applyfunc(derive)-companion*Phi
    for i in range(2):
        for j in range(2):
            checks.zero("Picard-Vessiot", f"fundamental matrix equation entry {i+1},{j+1}",
                        residual[i,j])
    sigma = {U:a*U, T:a**-2*T+b}
    for variable in (U,T):
        checks.zero("Picard-Vessiot", f"automorphism derivative compatibility on {variable}",
                    derive(sigma[variable])-derive(variable).subs(sigma, simultaneous=True))
    M = sp.Matrix([[a,a*b],[0,a**-1]])
    difference = Phi.subs(sigma, simultaneous=True)-Phi*M
    for i in range(2):
        for j in range(2):
            checks.zero("Picard-Vessiot", f"Borel action entry {i+1},{j+1}", difference[i,j])
    Mcd = sp.Matrix([[c,c*d],[0,c**-1]])
    composed = sp.Matrix([[a*c,a*c*(d+b/c**2)],[0,(a*c)**-1]])
    difference = M*Mcd-composed
    for i in range(2):
        for j in range(2):
            checks.zero("Picard-Vessiot", f"group law entry {i+1},{j+1}", difference[i,j])


def run() -> str:
    checks = Checks()
    critical_hierarchy(checks)
    euler_equation(checks)
    liouville_gauge(checks)
    schwarzian(checks)
    picard_vessiot(checks)
    counts = Counter(suite for suite, _ in checks.rows)
    lines = [
        "Transfinite Critical Potentials over the Surreals",
        "Exact finite algebra verification",
        f"Python {sys.version.split()[0]}; SymPy {sp.__version__}",
        "Arithmetic: exact symbolic expressions; no floating-point evaluations.",
        "",
    ]
    lines += [f"PASS | {suite} | {name}" for suite,name in checks.rows]
    lines += ["", "Suite counts:"]
    lines += [f"  {suite}: {count}" for suite,count in counts.items()]
    lines += [
        f"TOTAL: {len(checks.rows)} passed; 0 failed.",
        "",
        "Scope: finite identities only. This is not a proof-assistant verification.",
        "Transfinite summability, the imported derivation, exponent-field membership,",
        "and bibliographic novelty require the mathematical arguments and sources.",
    ]
    return "\n".join(lines)+"\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Also write the complete report to this file.")
    args = parser.parse_args()
    try:
        report = run()
        if args.output is not None:
            args.output.write_text(report, encoding="utf-8")
    except (AssertionError, OSError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        return 1
    print(report, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
