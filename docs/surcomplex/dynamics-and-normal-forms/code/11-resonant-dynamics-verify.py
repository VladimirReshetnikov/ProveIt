#!/usr/bin/env python3
"""Exact finite regression checks for Sharp Linearization at Surreal Scales.

These tests do NOT verify arbitrary-rank summability, class-sized statements,
all-period exclusion, novelty, or the full theorems. See article.pdf.
Requires Python 3.10+ and SymPy 1.14.0 (other versions may also work).
Writes a JSON and a text report to --output-dir (default: this directory).
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import platform
import random
import time

import sympy as sp

COUNTS: Counter[str] = Counter()
Y, U, D, W = sp.symbols("Y U D W")


def check(group: str, condition: bool, message: str) -> None:
    if not bool(condition):
        raise AssertionError(f"{group}: {message}")
    COUNTS[group] += 1


def zero(group: str, expression: sp.Expr, message: str) -> None:
    check(group, sp.cancel(sp.expand(expression)) == 0, message)


def mul(a: list[sp.Expr], b: list[sp.Expr], n: int) -> list[sp.Expr]:
    out = [sp.S.Zero] * (n + 1)
    for i, ai in enumerate(a[: n + 1]):
        if ai == 0:
            continue
        for j, bj in enumerate(b[: n + 1 - i]):
            if bj != 0:
                out[i + j] += ai * bj
    return [sp.expand(c) for c in out]


def powers(f: list[sp.Expr], n: int) -> list[list[sp.Expr]]:
    result = [[sp.S.One] + [sp.S.Zero] * n]
    for _ in range(n):
        result.append(mul(result[-1], f, n))
    return result


def conjugacy(f: list[sp.Expr], n: int) -> list[sp.Expr]:
    """Solve the normalized Schröder equation to degree n by its recursion."""
    lam = f[1]
    fp = powers(f, n)
    b = [sp.S.Zero, sp.S.One] + [sp.S.Zero] * (n - 1)
    for degree in range(2, n + 1):
        numerator = f[degree] + sum(
            b[k] * fp[k][degree] for k in range(2, degree)
        )
        b[degree] = sp.cancel(numerator / (lam - lam**degree))
    return b


def compose(a: list[sp.Expr], b: list[sp.Expr], n: int) -> list[sp.Expr]:
    bp = powers(b, n)
    return [sp.cancel(sum(a[k] * bp[k][j] for k in range(n + 1)))
            for j in range(n + 1)]


def input_coefficients(m: int, lam: sp.Expr,
                       coeffs: list[sp.Expr], n: int) -> list[sp.Expr]:
    f = [sp.S.Zero] * (n + 1)
    f[1] = lam
    for j, coefficient in enumerate(coeffs, start=1):
        degree = 1 + j * m
        if degree <= n:
            f[degree] = sp.sympify(coefficient)
    return f


def boundary_coefficients(m: int, cs: list[sp.Expr], n: int) -> list[sp.Expr]:
    beta = [sp.S.One]
    for k in range(1, n + 1):
        numerator = sum(cs[j - 1] * (1 + m * (k - j)) * beta[k - j]
                        for j in range(1, min(k, len(cs)) + 1))
        beta.append(sp.cancel(-numerator / (m * k)))
    return beta


def test_formal_conjugacy() -> None:
    cases = [
        (1, sp.Integer(2), [1, 2], 11),
        (1, sp.Integer(3), [-2, 1, 1], 10),
        (2, sp.Integer(-2), [1, -3], 13),
        (2, sp.Rational(-3, 2), [-2, 1], 11),
        (4, 2 * sp.I, [2, -1], 13),
    ]
    group = "formal_conjugacy"
    for m, lam, cs, n in cases:
        f = input_coefficients(m, lam, list(map(sp.sympify, cs)), n)
        b = conjugacy(f, n)
        lhs = compose(b, f, n)
        for k in range(n + 1):
            zero(group, lhs[k] - lam * b[k], f"m={m}, degree={k}")
            if k > 1 and (k - 1) % m:
                zero(group, b[k], f"equivariance m={m}, degree={k}")
        # Independently construct the formal inverse through a shorter degree.
        limit = min(8, n)
        bb = b[:limit + 1]
        inv = [sp.S.Zero, sp.S.One] + [sp.S.Zero] * (limit - 1)
        for k in range(2, limit + 1):
            inv[k] = -compose(bb, inv, limit)[k]
        for a, c in ((bb, inv), (inv, bb)):
            result = compose(a, c, limit)
            for k in range(limit + 1):
                zero(group, result[k] - (1 if k == 1 else 0),
                     f"inverse m={m}, degree={k}")


def test_parameter_reduction() -> None:
    group = "parameter_reduction"
    cases = [(1, 1, [1, 1], 7), (1, 1, [-2, 1], 7),
             (2, -1, [1, 1], 9), (2, -1, [-2, 1], 9),
             (4, sp.I, [1, 1], 9)]
    for m, zeta, cs, n in cases:
        f = input_coefficients(m, zeta + D,
                               [D * c for c in cs], n)
        b = conjugacy(f, n)
        beta = boundary_coefficients(m, list(map(sp.sympify, cs)), (n - 1) // m)
        for k in range(1, n + 1):
            p, q = sp.fraction(sp.cancel(b[k]))
            check(group, q.subs(D, 0) != 0,
                  f"regular coefficient m={m}, degree={k}")
            reduced = sp.cancel(p.subs(D, 0) / q.subs(D, 0))
            expected = beta[(k - 1) // m] if (k - 1) % m == 0 else 0
            zero(group, reduced - expected,
                 f"boundary limit m={m}, degree={k}")
        for k in range(1, 6):
            expression = sp.cancel((zeta + D) * (1 - (zeta + D)**(m*k)) / D)
            zero(group, expression.subs(D, 0) + m*k,
                 f"denominator residue m={m}, k={k}")


def test_boundary_differential() -> None:
    group = "boundary_differential"
    cases = [[1], [1, 1], [-2, 1], [-3, 2], [0, 0, 2]]
    for m in range(1, 6):
        for cs in cases:
            cs_s = list(map(sp.sympify, cs))
            beta = boundary_coefficients(m, cs_s, 10)
            B = sum(beta[k] * U**k for k in range(11))
            R = 1 + sum(c * U**j for j, c in enumerate(cs_s, 1))
            error = sp.Poly(sp.expand(R * (B + m*U*sp.diff(B, U)) - B), U)
            for k in range(11):
                zero(group, error.nth(k), f"vector field m={m}, k={k}, cs={cs}")
        # Explicit logarithmic derivatives, including the repeated-root case.
        for q in range(1, 5):
            R = 1 + 2*U**q
            candidate_log_derivative = -sp.Rational(1, m*q) * sp.diff(R, U) / R
            zero(group, candidate_log_derivative - (1/R - 1)/(m*U),
                 f"binomial formula m={m}, q={q}")
        R = (1-U)*(1-2*U)
        candidate = sp.Rational(1, m)/(U-1) - sp.Rational(2, m)/(U-sp.Rational(1, 2))
        zero(group, candidate - (1/R-1)/(m*U), f"two-root formula m={m}")
        R = (1-U)**2
        candidate = sp.Rational(1, m)/(1-U) + sp.Rational(1, m)/(1-U)**2
        zero(group, candidate - (1/R-1)/(m*U), f"repeated-root formula m={m}")
        R = 1+U+U**2
        for sign in [-1, 1]:
            root = (-1+sign*sp.I*sp.sqrt(3))/2
            alpha = sp.simplify(1/(m*root*sp.diff(R, U).subs(U, root)))
            expected = (-sp.Rational(1, 2)+sign*sp.I/(2*sp.sqrt(3)))/m
            zero(group, sp.simplify(alpha-expected), f"nonreal residue m={m}")
            check(group, sp.simplify(sp.im(alpha)) != 0, "residue is nonrational")


def test_iterate_quotient() -> None:
    group = "iterate_quotient"
    examples = [2*Y+Y**2, Y+Y**2, -Y+2*Y**2,
                Y/2-Y**2, Y+Y**2-2*Y**3]
    for psi in examples:
        it = Y
        mu = sp.diff(psi, Y).subs(Y, 0)
        for n in range(1, 4):
            it = sp.expand(psi.subs(Y, it))
            quotient, remainder = sp.div(it-Y, psi-Y, Y)
            zero(group, remainder, f"iterate divisibility n={n}, psi={psi}")
            zero(group, quotient.subs(Y, 0)-sum(mu**k for k in range(n)),
                 f"iterate quotient constant n={n}")
    psi = Y+D*(Y+Y**2)
    it = Y
    for n in range(1, 5):
        it = sp.expand(psi.subs(Y, it))
        quotient, remainder = sp.div(it-Y, psi-Y, Y)
        zero(group, remainder, f"parameter iterate divisibility n={n}")
        zero(group, quotient.subs(D, 0)-n, f"parameter quotient reduction n={n}")


def test_shell_identities() -> None:
    group = "shell_and_reciprocal"
    b1, b2 = sp.symbols("b1 b2", nonzero=True)
    for m, zeta in [(1, sp.S.One), (2, -sp.S.One), (4, sp.I)]:
        f = Y*(zeta+(Y**m-b1)*(Y**m-b2))
        zero(group, f.subs(Y, zeta*Y)-zeta*f, f"equivariance m={m}")
        for b in [b1, b2]:
            remainder = sp.rem(sp.expand(f-zeta*Y), Y**m-b, Y)
            zero(group, remainder, f"rotation roots m={m}, b={b}")
        numerator = W**(1+2*m)
        denominator = zeta*W**(2*m)+(1-b1*W**m)*(1-b2*W**m)
        zero(group, f.subs(Y, 1/W)*numerator-denominator,
             f"reciprocal map m={m}")
        zero(group, sp.diff(f, Y).subs(Y, 0)-(zeta+b1*b2),
             f"multiplier m={m}")
    # Ordinary rational specialization tests only the exact displayed identities;
    # it is not a model of infinitesimal valuations or of absence of other cycles.
    p, q = sp.Rational(1, 3), sp.Rational(1, 5)
    f = Y*(-1+(Y**2-p**2)*(Y**2-q**2))
    G = W**5 / (-W**4+(1-p**2*W**2)*(1-q**2*W**2))
    for z in [p, -p, q, -q]:
        zero(group, f.subs(Y, z)+z, f"explicit two-cycle {z}")
        zero(group, G.subs(W, 1/z)+1/z, f"explicit reciprocal cycle {z}")
    T = sp.symbols("T", nonzero=True)
    f = (-1+T**4)*Y-2*T**2*Y**3+Y**5
    zero(group, f+Y-Y*(Y**2-T**2)**2, "transcendental-example factorization")


def add(a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]) -> tuple[Fraction, Fraction]:
    return a[0]+b[0], a[1]+b[1]


def scale(a: tuple[Fraction, Fraction], k: Fraction) -> tuple[Fraction, Fraction]:
    return a[0]*k, a[1]*k


def test_lexicographic_scales() -> None:
    group = "lexicographic_scales"
    rng = random.Random(20260923)
    origin = (Fraction(0), Fraction(0))
    for trial in range(80):
        r, m = rng.randint(1, 5), rng.randint(1, 5)
        values = []
        for _ in range(r):
            a = Fraction(rng.randint(0, 3), rng.randint(1, 3))
            b = Fraction(rng.randint(1, 7) if a == 0 else rng.randint(-5, 5),
                         rng.randint(1, 4))
            values.append((a, b))
        delta = origin
        for rho in values:
            delta = add(delta, scale(rho, Fraction(m)))
        thresholds = []
        for j in range(1, r+1):
            # Coefficient of U^j in product(U-b_l): same-sign leading terms
            # when the ordinary amplitudes are positive, hence no cancellation.
            subset_values = []
            for subset in combinations(range(r), r-j):
                v = origin
                for ell in subset:
                    v = add(v, scale(values[ell], Fraction(m)))
                subset_values.append(v)
            coefficient_v = min(subset_values)
            threshold = scale(add(delta, scale(coefficient_v, Fraction(-1))),
                              Fraction(1, j*m))
            thresholds.append(threshold)
        check(group, max(thresholds) == max(values), f"sharp scale trial={trial}")
        L = add(delta, (Fraction(0), Fraction(1)))
        for size in range(r+1):
            for subset in combinations(range(r), size):
                exponent = L
                for ell in subset:
                    exponent = add(exponent, scale(values[ell], Fraction(-m)))
                check(group, exponent > origin, f"clearing exponent trial={trial}")
    epsilon, gamma = (Fraction(0), Fraction(1)), (Fraction(1), Fraction(0))
    for n in range(2, 42):
        b_value = add(gamma, scale(epsilon, Fraction(-n)))
        check(group, b_value > origin, f"positive coefficient sample n={n}")
        check(group, add(b_value, scale(epsilon, Fraction(n))) == gamma,
              f"support collision sample n={n}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    for function in [test_formal_conjugacy, test_parameter_reduction,
                     test_boundary_differential, test_iterate_quotient,
                     test_shell_identities, test_lexicographic_scales]:
        before = sum(COUNTS.values())
        function()
        print(f"PASS {function.__name__}: {sum(COUNTS.values())-before} assertions", flush=True)
    report = {
        "status": "PASS",
        "assertions": sum(COUNTS.values()),
        "groups": dict(COUNTS),
        "python": platform.python_version(),
        "sympy": sp.__version__,
        "utc_run_time": datetime.now(timezone.utc).isoformat(),
        "elapsed_seconds": round(time.monotonic()-start, 3),
        "scope": "Finite exact regression checks; not formal verification of the theorems.",
        "excluded": ["arbitrary-rank strong summability", "proper-class compatibility",
                     "all-period exclusion as a universal theorem", "novelty or priority"]
    }
    (args.output_dir/"verification.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    text = "Finite verification: PASS\n"+"\n".join(f"{k}: {v}" for k, v in COUNTS.items())
    text += f"\nTotal assertions: {report['assertions']}\nElapsed seconds: {report['elapsed_seconds']}\n"
    text += report["scope"]+"\n"
    (args.output_dir/"verification.txt").write_text(text, encoding="utf-8")
    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
