#!/usr/bin/env python3
"""Exact finite checks for the accompanying rank-one surcomplex article.

Requires only Python 3.10+ and its standard library.  All arithmetic is rational.
These checks do not formalize the infinite Hahn/Banach/Berkovich arguments.
Run: python verify_examples.py [--output verification.json]
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import platform

Series = list[Q]


def zero(n: int) -> Series:
    return [Q(0) for _ in range(n)]


def const(c: int | Q, n: int) -> Series:
    result = zero(n)
    result[0] = Q(c)
    return result


def add(a: Series, b: Series) -> Series:
    if len(a) != len(b):
        raise ValueError("Precision mismatch")
    return [x + y for x, y in zip(a, b)]


def neg(a: Series) -> Series:
    return [-x for x in a]


def mul(a: Series, b: Series) -> Series:
    n = len(a)
    if len(b) != n:
        raise ValueError("Precision mismatch")
    result = zero(n)
    for i, x in enumerate(a):
        if not x:
            continue
        for j, y in enumerate(b[: n - i]):
            if y:
                result[i + j] += x * y
    return result


def inv(a: Series) -> Series:
    if not a or not a[0]:
        raise ZeroDivisionError("Only series with a nonzero constant are units")
    result = zero(len(a))
    result[0] = 1 / a[0]
    for k in range(1, len(a)):
        result[k] = -sum(a[j] * result[k - j] for j in range(1, k + 1)) / a[0]
    return result


def scale(a: Series, c: int) -> Series:
    return [c * x for x in a]


def normalized_theta_coefficients(m: int, precision: int) -> list[Series]:
    """Coefficients in U of t^(m(m-1)) F(t^(-(2m-1)) U), with q=t^2."""
    if m < 1 or precision < 1:
        raise ValueError("m and precision must be positive")
    result: list[Series] = []
    k = 0
    while True:
        exponent = (k - m) * (k - m + 1) // 2
        if k >= m and exponent >= precision:
            break
        term = zero(precision)
        if exponent < precision:
            term[exponent] = 1
        result.append(term)
        k += 1
    return result


def evaluate(coefficients: list[Series], u: Series) -> Series:
    result = zero(len(u))
    for coefficient in reversed(coefficients):
        result = add(mul(result, u), coefficient)
    return result


def root_series(m: int, precision: int) -> tuple[Series, int]:
    coefficients = normalized_theta_coefficients(m, precision)
    derivative = [scale(coefficients[k], k) for k in range(1, len(coefficients))]
    u = const(-1, precision)
    iterations = 0
    # A simple root modulo q guarantees formal Newton convergence.
    # This loop is bounded defensively; no unbounded symbolic search is used.
    for _ in range(precision + 1):
        residual = evaluate(coefficients, u)
        if not any(residual):
            return u, iterations
        slope = evaluate(derivative, u)
        u = add(u, neg(mul(residual, inv(slope))))
        iterations += 1
    raise ArithmeticError(f"Newton iteration did not reach precision {precision}")


def serialize_series(u: Series) -> dict[str, str]:
    return {str(k): str(coefficient) for k, coefficient in enumerate(u) if coefficient}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification.json"))
    args = parser.parse_args()
    checks: list[dict[str, object]] = []
    roots: list[dict[str, object]] = []

    def check(name: str, condition: bool) -> None:
        checks.append({"name": name, "passed": bool(condition)})
        if not condition:
            raise AssertionError(name)

    for m in range(1, 9):
        leading = m * (m + 1) // 2
        precision = leading + 8
        u, iterations = root_series(m, precision)
        coefficients = normalized_theta_coefficients(m, precision)
        check(f"root {m}: exact residual modulo q^{precision}",
              not any(evaluate(coefficients, u)))
        check(f"root {m}: constant -1", u[0] == -1)
        check(f"root {m}: first correction exponent", not any(u[1:leading]))
        check(f"root {m}: first correction sign", u[leading] == (-1) ** m)
        derivative = [scale(coefficients[k], k) for k in range(1, len(coefficients))]
        check(f"root {m}: derivative leading coefficient",
              evaluate(derivative, u)[0] == (-1) ** (m - 1))
        roots.append({"m": m, "precision_q": precision, "newton_steps": iterations,
                      "coefficients": serialize_series(u)})

    first = {int(k): Q(v) for k, v in roots[0]["coefficients"].items()}
    known = [-1, -1, -2, -4, -9, -21, -52]
    check("first root: displayed partial-theta coefficients through q^6",
          all(first.get(k, Q(0)) == x for k, x in enumerate(known)))

    for m in range(1, 41):
        at_break = [Q(n * n - (2 * m - 1) * n) for n in range(2 * m + 10)]
        minimum = min(at_break)
        active = [n for n, value in enumerate(at_break) if value == minimum]
        check(f"Newton corner {m}: active indices m-1,m", active == [m - 1, m])
        between = [Q(n * n - 2 * m * n) for n in range(2 * m + 10)]
        check(f"Newton interval {m}: active index m",
              [n for n, value in enumerate(between) if value == min(between)] == [m])

    # Finite tests of the elementary quadratic-tail formula.  The article
    # proves its infinite version by monotonicity rather than by these tests.
    for numerator in range(-20, 21):
        beta = Q(numerator, 3)
        n0 = max(0, int(-beta / 2) + 2)
        for n in range(n0, n0 + 6):
            claimed = Q((n + 1) ** 2) + (n + 1) * beta
            observed = min(Q(k * k) + k * beta for k in range(n + 1, n + 80))
            check(f"tail beta={beta},N={n}", claimed == observed)

    # Residue pullback under Z=c W^m: a monomial Z^n dZ has a W^-1
    # coefficient exactly when n=-1, and that coefficient is multiplied by m.
    for m in range(1, 8):
        for n in range(-12, 13):
            pullback_exponent = m * (n + 1) - 1
            check(f"residue pullback m={m},n={n}",
                  (pullback_exponent == -1) == (n == -1))

    report = {
        "purpose": "Exact finite checks; not a formal verification of the article",
        "python": platform.python_version(),
        "arithmetic": "fractions.Fraction; no floating-point arithmetic",
        "checks": len(checks),
        "passed": sum(bool(item["passed"]) for item in checks),
        "root_expansions": roots,
        "check_results": checks,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {report['passed']}/{report['checks']} exact finite checks.")
    for root in roots[:4]:
        print(f"m={root['m']}, U_m coefficients: {root['coefficients']}")
    print(f"Report written to {args.output.resolve()}")


if __name__ == "__main__":
    main()
