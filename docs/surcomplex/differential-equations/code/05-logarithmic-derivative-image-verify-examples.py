#!/usr/bin/env python3
"""Exact finite checks for the accompanying surreal differential-algebra article.

These tests check algebraic identities, finite differential formulas, and the
restricted rational-phase classifier. They do not verify the construction of
surreal numbers, strong summability, the Berarducci--Mantova derivation, or any
infinite/proper-class theorem. Ordinary symbolic differentiation is used only
for identities that specialize under the proved derivation rules.

Run from any directory:
    python code/verify_examples.py
The JSON report is written to data/verification.json beside the article.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
from typing import Callable

import sympy as sp
from sympy.polys.polyerrors import CoercionFailed, PolynomialError


@dataclass(frozen=True)
class PhaseDecision:
    """Exact rational-input decision; not a universal surreal decision type."""

    admissible: bool
    normalized_expression: str
    degree_gap: int | None
    reason: str


def classify_rational_phase(expr: sp.Expr, variable: sp.Symbol) -> PhaseDecision:
    """Classify b(variable) with b in Q(variable) by its degree at infinity.

    For q=a+i*b in the article, this decides whether D*y=q*y has a nonzero
    surcomplex solution. The real part a is unrestricted by the theorem.
    Inputs outside Q(variable) raise ValueError, not an inadmissible verdict.
    This API accepts trusted SymPy expressions, not text from untrusted users.
    """
    if not isinstance(variable, sp.Symbol):
        raise TypeError("variable must be a SymPy Symbol")
    if not isinstance(expr, sp.Expr):
        raise TypeError("expr must be a SymPy Expr (not an untrusted string)")
    if expr.has(sp.nan, sp.zoo, sp.oo, -sp.oo):
        raise ValueError("non-finite symbolic input is outside Q(variable)")
    if expr.free_symbols - {variable}:
        raise ValueError("parameters outside Q(variable) are unsupported")
    normalized = sp.cancel(expr)
    numerator, denominator = sp.fraction(normalized)
    try:
        p = sp.Poly(numerator, variable, domain=sp.QQ)
        q = sp.Poly(denominator, variable, domain=sp.QQ)
    except (PolynomialError, CoercionFailed, TypeError, ValueError) as exc:
        raise ValueError("input is outside the implemented Q(variable) domain") from exc
    if q.is_zero:
        raise ValueError("zero denominator")
    if p.is_zero:
        return PhaseDecision(True, str(normalized), None, "zero imaginary coefficient")
    gap = int(q.degree() - p.degree())
    return PhaseDecision(
        gap >= 2,
        str(normalized),
        gap,
        "finite primitive iff denominator degree minus numerator degree is at least 2",
    )


class Checks:
    def __init__(self) -> None:
        self.results: list[dict[str, object]] = []

    def check(self, name: str, predicate: bool, detail: str = "") -> None:
        self.results.append({"name": name, "passed": bool(predicate), "detail": detail})

    def equal(self, name: str, left: sp.Expr, right: sp.Expr) -> None:
        residual = sp.simplify(sp.expand(left - right))
        self.check(name, residual == 0, "residual = " + str(residual))

    def rejects(self, name: str, operation: Callable[[], object]) -> None:
        try:
            operation()
        except (ValueError, TypeError) as exc:
            self.check(name, True, type(exc).__name__ + ": " + str(exc))
        else:
            self.check(name, False, "unsupported input was accepted")


def run_checks() -> dict[str, object]:
    c = Checks()
    x = sp.Symbol("x", positive=True, real=True)
    t = sp.Symbol("t", positive=True, real=True)
    z = sp.Symbol("z", real=True)
    I = sp.I
    D_t = lambda expr: -t**2 * sp.diff(expr, t)

    # Real-power formulas, with t = 1/x and D*x = 1.
    powers = [sp.Rational(n, d) for d in (1, 2, 3) for n in range(-4, 6)]
    for r in sorted(set(powers)):
        c.equal(f"power rule r={r}", D_t(t**r), -r*t**(r+1))
    for p in (sp.Rational(-3), sp.Rational(0), sp.Rational(1, 2),
              sp.Rational(3, 2), sp.Rational(2), sp.Rational(5)):
        primitive = x**(1-p)/(1-p)
        c.equal(f"power primitive p={p}", sp.diff(primitive, x), x**(-p))
    c.equal("logarithmic primitive", sp.diff(sp.log(x), x), 1/x)

    # Every listed rational decision is finite exact polynomial arithmetic.
    phase_examples = [
        (sp.S.Zero, True), (sp.S.One, False), (1/x, False), (1/x**2, True),
        (x/(1+x**2), False), (1/(1+x**2), True),
        ((1-x**2)/(1+x**2)**2, True),
        ((x-1)/(x**3-x**2), True),
        ((x**4-1)/(x**2-1), False),
        (1/(x**5+2*x+1), True), (-3/x, False), (sp.Rational(7, 3)/x**2, True),
    ]
    for k, (expr, expected) in enumerate(phase_examples):
        decision = classify_rational_phase(expr, x)
        c.check(f"rational phase example {k}: {expr}",
                decision.admissible == expected, json.dumps(asdict(decision)))
    for n in range(6):
        for m in range(6):
            # Nonzero leading terms guarantee the expected infinity order;
            # common-factor cancellation leaves their degree difference invariant.
            expr = (x**n + 2)/(x**m + 3)
            decision = classify_rational_phase(expr, x)
            c.check(f"rational degree pair n={n},m={m}",
                    decision.admissible == (m-n >= 2) and decision.degree_gap == m-n,
                    json.dumps(asdict(decision)))
    for name, expr in [
        ("sine", sp.sin(x)), ("logarithm", sp.log(x)),
        ("algebraic coefficient beyond Q", sp.sqrt(2)/x**2),
        ("unbound parameter", z/x**2), ("exponential", sp.exp(x)),
        ("undefined value", sp.nan), ("infinite value", sp.zoo),
    ]:
        c.rejects("reject unsupported " + name,
                  lambda expr=expr: classify_rational_phase(expr, x))
    c.rejects("reject string input", lambda: classify_rational_phase("1/x", x))

    # Finite-depth logarithmic primitive identities. These do not numerically
    # substitute infinite x or decide general logarithmic coefficient expressions.
    logs = [x]
    for _ in range(3):
        logs.append(sp.log(logs[-1]))
    for k in range(3):
        prefactor = sp.prod(logs[:k])
        for p in (2, 3):
            primitive = logs[k]**(1-p)/(1-p)
            c.equal(f"iterated-log primitive k={k},p={p}",
                    sp.diff(primitive, x), 1/(prefactor*logs[k]**p))
        c.equal(f"iterated-log threshold primitive k={k},p=1",
                sp.diff(logs[k+1], x), 1/(prefactor*logs[k]))

    # Algebraic unit and its logarithmic derivative.
    y = (1+I*x)/sp.sqrt(1+x**2)
    c.equal("algebraic phase norm", y*sp.conjugate(y), sp.S.One)
    c.equal("algebraic phase logarithmic derivative", sp.diff(y, x)/y, I/(1+x**2))
    c.equal("rational finite primitive", sp.diff(x/(1+x**2), x),
            (1-x**2)/(1+x**2)**2)

    # Truncations of Exp_0(-i*t). The exact residual has one nonzero term;
    # a vanishing residual is neither expected nor asserted for a truncation.
    for n in range(13):
        E = sum(((-I*t)**k/sp.factorial(k) for k in range(n+1)), sp.S.Zero)
        expected = -I*(-I)**n*t**(n+2)/sp.factorial(n)
        c.equal(f"exponential truncation residual N={n}", D_t(E)-I*t**2*E, expected)
        unit_prefix = sp.series(E*sp.conjugate(E)-1, t, 0, n+1).removeO()
        c.equal(f"unit-norm truncation through N={n}", unit_prefix, sp.S.Zero)

    # Separate scalar and external analytic differentiation.
    F = t**2*sp.exp(z)
    evaluated = F.subs(z, t)
    scalar_part = D_t(F).subs(z, t)
    argument_part = D_t(t)*sp.diff(F, z).subs(z, t)
    c.equal("moving evaluation total chain rule", D_t(evaluated), scalar_part+argument_part)
    c.equal("moving evaluation displayed residual", D_t(evaluated),
            (-2*t**3-t**4)*sp.exp(t))
    c.equal("commuting scalar and analytic derivatives", D_t(sp.diff(F, z)),
            sp.diff(D_t(F), z))
    c.equal("fixed-contour sample coefficient", D_t(2*sp.pi*I*t), -2*sp.pi*I*t**2)
    F2 = x*z**2+z/x
    h = 1/x
    c.equal("polynomial moving evaluation", sp.diff(F2.subs(z, h), x),
            sp.diff(F2, x).subs(z, h)+sp.diff(h, x)*sp.diff(F2, z).subs(z, h))

    # Constant-polynomial operator; only listed real-root solutions are tested.
    T = sp.Symbol("T")
    P = sp.Poly((T-2)**2*(T+1)*(T**2+1), T)
    def apply_operator(f: sp.Expr) -> sp.Expr:
        return sp.Add(*(coefficient*sp.diff(f, x, exponent[0])
                        for exponent, coefficient in P.terms()))
    for name, f in [("exp(2x)", sp.exp(2*x)), ("x exp(2x)", x*sp.exp(2*x)),
                    ("exp(-x)", sp.exp(-x))]:
        c.equal("constant-polynomial solution " + name, apply_operator(f), sp.S.Zero)
    for n in range(1, 8):
        c.equal(f"polynomial primitive kernel m={n}", sp.diff(x**(n-1), x, n), sp.S.Zero)

    N = sp.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    A = 2*sp.eye(3)+N
    Y = sp.exp(2*x)*(sp.eye(3)+x*N+x**2*N**2/2)
    residual = Y.diff(x)-A*Y
    for row in range(3):
        for column in range(3):
            c.equal(f"real Jordan fundamental matrix ({row},{column})",
                    residual[row, column], sp.S.Zero)
    c.equal("real Jordan determinant", Y.det(), sp.exp(6*x))

    # An inadmissible homogeneous coefficient can still have a unique
    # particular solution in an inhomogeneous equation.
    c.equal("inhomogeneous particular solution y=i", sp.diff(I, x)-I*I, sp.S.One)

    failed = [r for r in c.results if not r["passed"]]
    return {
        "description": "Exact finite checks; not a formal verification of the article",
        "executed_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": platform.python_version(),
        "sympy_version": sp.__version__,
        "check_count": len(c.results),
        "passed": len(c.results)-len(failed),
        "failed": len(failed),
        "all_passed": not failed,
        "scope_exclusions": [
            "No construction of the full surreal field or its derivation is implemented.",
            "No strong-summability or proper-class theorem is machine-checked.",
            "Ordinary symbolic oscillatory functions are not interpreted as surcomplex solutions.",
            "The decision procedure implements Q(x), not arbitrary exact reals or transseries.",
        ],
        "checks": c.results,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"verification.json")
    args = parser.parse_args()
    report = run_checks()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(f"{report['passed']}/{report['check_count']} checks passed; {report['failed']} failed.")
    print(f"Report: {args.output}")
    for check in report["checks"]:
        if not check["passed"]:
            print("FAILED:", check["name"], check["detail"])
    return 0 if report["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
