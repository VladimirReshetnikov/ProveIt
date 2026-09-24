#!/usr/bin/env python3
"""Finite exact checks accompanying article.tex.

This is not a surreal-number implementation or a formal proof checker.  The
identification D = -t**2*d/dt, and its embedding at t = omega**(-1), are proved
in the article.  All computations here are exact symbolic algebra.
"""
from __future__ import annotations

import argparse
import json
import platform
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

try:
    import sympy as s
except ImportError as exc:
    raise SystemExit("SymPy is required. Install it with: python -m pip install sympy") from exc

T = s.Symbol("t", positive=True)
W = s.Symbol("w", positive=True)
Z = s.Symbol("Z")
I = s.I
CHECKS: list[dict[str, object]] = []


def D(expr: s.Expr) -> s.Expr:
    """The exact Laurent derivation corresponding to d/domega."""
    return s.expand(-T**2 * s.diff(expr, T))


def iterate(op: Callable[[s.Expr], s.Expr], expr: s.Expr, n: int) -> s.Expr:
    if n < 0:
        raise ValueError("Iteration count must be nonnegative")
    for _ in range(n):
        expr = op(expr)
    return expr


def truncate(expr: s.Expr, order: int) -> s.Expr:
    """Reduce a polynomial in t modulo t**order (exact, no numerical limit)."""
    if order < 1:
        raise ValueError("Order must be positive")
    poly = s.Poly(s.expand(expr), T)
    return s.Add(*(coefficient * T**power[0]
                   for power, coefficient in poly.terms() if power[0] < order))


def exp_small(h: s.Expr, order: int) -> s.Expr:
    if s.expand(h).coeff(T, 0) != 0:
        raise ValueError("The input must have zero constant coefficient")
    value, power = s.Integer(1), s.Integer(1)
    for k in range(1, order):
        power = truncate(power*h, order)
        value += power/s.factorial(k)
    return truncate(value, order)


def log_one_plus(h: s.Expr, order: int) -> s.Expr:
    if s.expand(h).coeff(T, 0) != 0:
        raise ValueError("The input must have zero constant coefficient")
    value, power = s.Integer(0), s.Integer(1)
    for k in range(1, order):
        power = truncate(power*h, order)
        value += (-1)**(k+1)*power/s.Integer(k)
    return truncate(value, order)


def check(group: str, name: str, residual: s.Expr | s.MatrixBase) -> None:
    """Record one identity; a matrix identity is counted as one check."""
    try:
        if isinstance(residual, s.MatrixBase):
            reduced = residual.applyfunc(s.simplify)
            passed = reduced == s.zeros(*reduced.shape)
        else:
            reduced = s.simplify(residual)
            passed = reduced == 0
        record: dict[str, object] = {"group": group, "name": name, "passed": bool(passed)}
        if not passed:
            record["nonzero_residual"] = str(reduced)
    except Exception as exc:
        record = {"group": group, "name": name, "passed": False,
                  "error": f"{type(exc).__name__}: {exc}"}
    CHECKS.append(record)


def resolvent_prefix(f: s.Expr, lam: s.Expr, n: int) -> s.Expr:
    if lam == 0:
        raise ValueError("A resolvent requires a nonzero constant lambda")
    term, result = f, s.Integer(0)
    for j in range(n+1):
        result -= term / lam**(j+1)
        term = D(term)
    return s.expand(result)


def coefficient_solution(f: s.Expr, lam: s.Expr, lower: int, upper: int) -> s.Expr:
    """Compute y modulo t**(upper+1), given a valid lower exponent bound."""
    if lam == 0 or upper < lower:
        raise ValueError("Need lambda != 0 and upper >= lower")
    expanded = s.expand(f)
    previous, result = s.Integer(0), s.Integer(0)
    for n in range(lower, upper+1):
        current = s.simplify(-(expanded.coeff(T, n) + (n-1)*previous)/lam)
        result += current*T**n
        previous = current
    return s.expand(result)


def run_checks() -> None:
    # Monomials and product rules, including a principal Laurent part.
    for n in range(-12, 13):
        check("derivation", f"D(t^{n})", D(T**n) + n*T**(n+1))
    for n in range(13):
        check("derivation", f"D^{n}(t)",
              iterate(D, T, n) - (-1)**n*s.factorial(n)*T**(n+1))
    pairs = [(T + T**3, T**-2 + I*T),
             (1/(1-T), T**3/(1+T)),
             (T**-3 + 2 + 7*T, 1 - I*T**4)]
    for j, (f, g) in enumerate(pairs):
        check("derivation", f"product rule {j}", D(f*g)-D(f)*g-f*D(g))

    # Laurent integration: no t**1 coefficient is present in these inputs.
    for j, f in enumerate([T**-3 + 2 + I*T**2 + 4*T**7,
                           -7*T**-1 + 3*T**3, T**2 + T**3 + T**4]):
        expanded = s.expand(f)
        primitive = s.Add(*(expanded.coeff(T, n)*T**(n-1)/s.Integer(1-n)
                            for n in range(-5, 9) if n != 1))
        check("integration", f"Laurent primitive {j}", D(primitive)-f)
    for p in map(s.Rational, [-2, -1, 0, s.Rational(1, 2),
                              s.Rational(3, 2), 2, 5]):
        primitive = W**(1-p)/(1-p)
        check("integration", f"power primitive p={p}", s.diff(primitive, W)-W**(-p))
    check("integration", "logarithmic endpoint", s.diff(s.log(W), W)-1/W)
    ell, product = W, s.Integer(1)
    for n in range(1, 5):
        product *= ell
        ell = s.log(ell)
        check("integration", f"logarithmic tower n={n}", s.diff(ell, W)-1/product)

    # Infinitesimal formal identities are checked only modulo a specified power.
    h, k = T + I*T**2, 2*T**2 - T**3
    theta = T + T**2 + 2*T**3
    for order in [4, 6, 8, 10]:
        eh, ek = exp_small(h, order), exp_small(k, order)
        lh = log_one_plus(h, order)
        check("formal_series", f"exp group law mod t^{order}",
              truncate(exp_small(h+k, order)-eh*ek, order))
        check("formal_series", f"log(exp(h)) mod t^{order}",
              truncate(log_one_plus(eh-1, order)-h, order))
        check("formal_series", f"exp(log(1+h)) mod t^{order}",
              truncate(exp_small(lh, order)-(1+h), order))
        check("formal_series", f"exp derivative mod t^{order}",
              truncate(D(eh)-eh*D(h), order))
        check("formal_series", f"log derivative mod t^{order}",
              truncate((1+h)*D(lh)-D(h), order))
        check("formal_series", f"unit phase norm mod t^{order}",
              truncate(exp_small(I*theta, order)*exp_small(-I*theta, order)-1, order))

    # Total derivatives: the two derivations act on independent symbols.
    families = [W*Z**2 + Z/W,
                W**2/(Z-1) + s.exp(W)*Z**3,
                s.log(W)*Z + W**-2*Z**4]
    points = [1+1/W, 2+1/W, 1+2/W]
    for j, (family, point) in enumerate(zip(families, points)):
        left = s.diff(family.subs(Z, point), W)
        right = s.diff(family, W).subs(Z, point) + s.diff(family, Z).subs(Z, point)*s.diff(point, W)
        check("coherent_calculus", f"total chain rule {j}", left-right)
        check("coherent_calculus", f"commuting partial derivations {j}",
              s.diff(s.diff(family, W), Z)-s.diff(s.diff(family, Z), W))
    check("coherent_calculus", "displayed moving coefficient example",
          s.diff(families[0].subs(Z, points[0]), W) - (1-2/W**2-2/W**3))
    a, z = W**2 + I/W, 1+1/W
    check("coherent_calculus", "moving pole",
          s.diff(1/(z-a), W)+(s.diff(z,W)-s.diff(a,W))/(z-a)**2)

    # General exact finite residuals, not only the displayed factorial example.
    examples = [T, -3/T**2+2+5*T+I*T**3, T**-5-2/T+7*T**2]
    for lam in [I, s.Integer(2), 1+I]:
        for j, f in enumerate(examples):
            for n in range(9):
                y = resolvent_prefix(f, lam, n)
                target = f-iterate(D, f, n+1)/lam**(n+1)
                check("resolvent", f"lambda={lam}, input={j}, N={n}", D(y)-lam*y-target)
    for n in range(13):
        y = s.Add(*(I**(j+1)*s.factorial(j)*T**(j+1) for j in range(n+1)))
        residual = -I**(-(n+1))*(-1)**(n+1)*s.factorial(n+1)*T**(n+2)
        check("factorial_example", f"factorial residual N={n}", D(y)-I*y-T-residual)

    for lam in [I, s.Integer(2), 1+I]:
        for j, (f, lower) in enumerate(zip(examples, [1, -2, -5])):
            upper = 10
            y = coefficient_solution(f, lam, lower, upper)
            residual = s.expand(D(y)-lam*y-f)
            # One whole-prefix identity is one check, not one per coefficient.
            checked_prefix = s.Add(*(residual.coeff(T, n)*T**n
                                     for n in range(lower, upper+1)))
            check("coefficient_recursion", f"lambda={lam}, input={j}, through t^{upper}", checked_prefix)

    # Real exponential-polynomial modes. These do not test nonexistence claims.
    for r in [s.Integer(-2), s.Integer(0), s.Rational(3,2)]:
        for m in range(1, 5):
            for degree in range(m):
                y = s.exp(r*W)*W**degree
                op = lambda x, r=r: s.simplify(s.diff(x,W)-r*x)
                check("constant_operators", f"r={r}, multiplicity={m}, degree={degree}", iterate(op,y,m))
    for j, y in enumerate([s.Integer(1), s.exp(W), W*s.exp(W)]):
        result = s.diff(y,W)
        result = s.diff(result,W)-result
        result = s.diff(result,W)-result
        result = s.diff(result,W,2)+result
        check("constant_operators", f"mixed fifth-order example, basis={j}", result)

    for size in range(1, 6):
        nilpotent = s.zeros(size)
        for j in range(size-1):
            nilpotent[j,j+1] = 1
        B = s.eye(size)
        Binv = s.eye(size)
        for power in range(1,size):
            B += W**power*nilpotent**power/s.factorial(power)
            Binv += (-W)**power*nilpotent**power/s.factorial(power)
        check("matrix_systems", f"nilpotent exponential inverse, size={size}", B*Binv-s.eye(size))
        for r in [s.Integer(-1), s.Integer(0), s.Integer(3)]:
            fundamental = s.exp(r*W)*B
            A = r*s.eye(size)+nilpotent
            check("matrix_systems", f"Jordan derivative, size={size}, r={r}",
                  fundamental.diff(W)-A*fundamental)
            check("matrix_systems", f"Jordan determinant, size={size}, r={r}",
                  fundamental.det()-s.exp(size*r*W))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"verification.json")
    args = parser.parse_args()
    run_checks()
    passed = sum(bool(c["passed"]) for c in CHECKS)
    report = {
        "title": "Finite exact verification for intrinsic surreal differential calculus",
        "scope": "Finite symbolic identities and formal truncations; not a formal verification of the general theorems.",
        "utc_timestamp": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "sympy": s.__version__,
        "checks": len(CHECKS), "passed": passed, "failed": len(CHECKS)-passed,
        "results": CHECKS,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print(f"Python {report['python']}; SymPy {report['sympy']}")
    print(report["scope"])
    for group, total in Counter(str(c["group"]) for c in CHECKS).items():
        successes = sum(bool(c["passed"]) for c in CHECKS if c["group"] == group)
        print(f"{group}: {successes}/{total}")
    print(f"TOTAL: {passed}/{len(CHECKS)} passed; {len(CHECKS)-passed} failed")
    for entry in CHECKS:
        if not entry["passed"]:
            print("FAIL:", entry)
    print("JSON report:", args.output)
    return 0 if passed == len(CHECKS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
