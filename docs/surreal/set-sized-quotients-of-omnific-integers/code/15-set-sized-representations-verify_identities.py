#!/usr/bin/env python3
"""Exact finite checks accompanying the omnific representation manuscript.

This is NOT a surreal-number implementation or a verification of the infinite
Hahn-support or Hartogs arguments. Exponents are pairs (a,b) in Q^2, interpreted
as a+b/omega and ordered lexicographically. All polynomials here are finite.

Run: python3 verify_identities.py --output finite_checks.json
Requires Python >= 3.9; no external packages are used.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from fractions import Fraction as F
from pathlib import Path
from typing import Dict, Tuple

Exp = Tuple[F, F]
Poly = Dict[Exp, F]
Matrix = Tuple[Tuple[F, F], Tuple[F, F]]
ZERO_EXP: Exp = (F(0), F(0))
SEED = 20260923


def exp_add(a: Exp, b: Exp) -> Exp:
    return a[0] + b[0], a[1] + b[1]


def exp_scale(n: int, a: Exp) -> Exp:
    return n * a[0], n * a[1]


def monomial(e: Exp, c: F = F(1)) -> Poly:
    return {} if c == 0 else {e: c}


def plus(p: Poly, q: Poly) -> Poly:
    out = dict(p)
    for e, c in q.items():
        out[e] = out.get(e, F(0)) + c
        if out[e] == 0:
            del out[e]
    return out


def minus(p: Poly, q: Poly) -> Poly:
    return plus(p, {e: -c for e, c in q.items()})


def times(p: Poly, q: Poly) -> Poly:
    out: Poly = {}
    for e, c in p.items():
        for f, d in q.items():
            g = exp_add(e, f)
            out[g] = out.get(g, F(0)) + c * d
            if out[g] == 0:
                del out[g]
    return out


def shift(p: Poly, e: Exp) -> Poly:
    return {exp_add(f, e): c for f, c in p.items()}


def ct(p: Poly) -> F:
    return p.get(ZERO_EXP, F(0))


def coefficient_sum(p: Poly) -> F:
    return sum(p.values(), F(0))


def random_poly(rng: random.Random, pure: bool = False) -> Poly:
    """Generate nonnegative support, with an integer constant coefficient."""
    p: Poly = {}
    for _ in range(rng.randrange(1, 9)):
        first = F(rng.randrange(1 if pure else 0, 5))
        second = F(rng.randrange(-5 if first > 0 else 0, 6), rng.randrange(1, 5))
        e = (first, second)
        c = F(rng.randrange(-7, 8), 1 if e == ZERO_EXP else rng.randrange(1, 6))
        p = plus(p, monomial(e, c))
    if not pure:
        p = plus(p, monomial(ZERO_EXP, F(rng.randrange(-7, 8))))
    if pure and not p:
        p = monomial((F(1), F(0)))
    return p


def matrix_add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2))  # type: ignore[return-value]


def matrix_scale(c: F, a: Matrix) -> Matrix:
    return tuple(tuple(c * a[i][j] for j in range(2)) for i in range(2))  # type: ignore[return-value]


def matrix_times(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(2)), F(0))
                       for j in range(2)) for i in range(2))  # type: ignore[return-value]


IDENTITY: Matrix = ((F(1), F(0)), (F(0), F(1)))


def gaussian_image(x: Poly, y: Poly, j: Matrix) -> Matrix:
    return matrix_add(matrix_scale(ct(x), IDENTITY), matrix_scale(ct(y), j))


def expect(condition: bool, label: str) -> None:
    if not condition:
        raise AssertionError(label)


def run_checks() -> dict:
    rng = random.Random(SEED)
    groups: Dict[str, int] = {}
    failures = []

    def run(group: str, number: int, callback) -> None:
        try:
            callback()
            groups[group] = groups.get(group, 0) + 1
        except Exception as exc:
            failures.append({"group": group, "case": number,
                             "error": f"{type(exc).__name__}: {exc}"})

    # The explicit obstruction's finite telescoping formula, for every N <= 120.
    for n_terms in range(1, 121):
        def explicit(n_terms=n_terms):
            u = monomial((F(0), F(2)))
            v = monomial((F(0), F(1)))
            qn: Poly = {}
            for n in range(n_terms):
                qn = plus(qn, monomial((F(1), F(-(n + 2)))))
            expected = minus(monomial((F(1), F(0))),
                             monomial((F(1), F(-n_terms))))
            expect(times(minus(u, v), qn) == expected, "explicit telescoping")
            expect(all(e > (F(1, 2), F(0)) for e in qn), "quotient exponent bound")
            expect(coefficient_sum(expected) == 0, "finite evaluation is consistent")
        run("explicit_truncations", n_terms, explicit)

    # Multiplication of the generic finite geometric inverse by an arbitrary X.
    for number in range(1, 181):
        x = random_poly(rng, pure=True)
        b = (F(0), F(rng.randrange(1, 10), rng.randrange(1, 8)))
        d = (F(0), F(rng.randrange(1, 10), rng.randrange(1, 8)))
        a = exp_add(b, d)
        n_terms = rng.randrange(1, 35)

        def divisor(x=x, a=a, b=b, d=d, n_terms=n_terms):
            gn: Poly = {}
            for n in range(n_terms):
                gn = plus(gn, monomial(exp_scale(-n, d)))
            qn = times(shift(x, exp_scale(-1, a)), gn)
            lhs = times(minus(monomial(a), monomial(b)), qn)
            rhs = minus(x, shift(x, exp_scale(-n_terms, d)))
            expect(lhs == rhs, "generic finite divisor identity")
            expect(all(e > ZERO_EXP for e in qn), "positive quotient support")
        run("generic_divisor_truncations", number, divisor)

    for number in range(1, 201):
        p, q = random_poly(rng), random_poly(rng)

        def augmentation(p=p, q=q):
            expect(ct(times(p, q)) == ct(p) * ct(q), "constant term of product")
            expect(ct(plus(p, q)) == ct(p) + ct(q), "constant term of sum")
        run("constant_term_laws", number, augmentation)

    for number in range(1, 201):
        p, q = random_poly(rng), random_poly(rng)

        def evaluation(p=p, q=q):
            expect(coefficient_sum(times(p, q)) == coefficient_sum(p) * coefficient_sum(q),
                   "finite-support evaluation is multiplicative")
            expect(coefficient_sum(plus(p, q)) == coefficient_sum(p) + coefficient_sum(q),
                   "finite-support evaluation is additive")
        run("finite_support_evaluation", number, evaluation)

    for number in range(1, 121):
        x, y, u, v = (random_poly(rng) for _ in range(4))
        t = F(rng.randrange(-10, 11), rng.randrange(1, 8))
        j: Matrix = ((t, -1 - t * t), (F(1), -t))

        def gaussian(x=x, y=y, u=u, v=v, j=j):
            expect(matrix_times(j, j) == matrix_scale(F(-1), IDENTITY), "J squared")
            re = minus(times(x, u), times(y, v))
            im = plus(times(x, v), times(y, u))
            lhs = gaussian_image(re, im, j)
            rhs = matrix_times(gaussian_image(x, y, j), gaussian_image(u, v, j))
            expect(lhs == rhs, "Gaussian evaluation in a noncommutative ring")
        run("gaussian_matrix_representations", number, gaussian)

    return {
        "status": "PASS" if not failures else "FAIL",
        "seed": SEED,
        "python_version": sys.version.split()[0],
        "passed_test_cases": sum(groups.values()),
        "failed_test_cases": len(failures),
        "groups": groups,
        "failures": failures,
        "arithmetic": "Exact fractions; finite dictionaries of exponents in lexicographic Q^2",
        "scope": "Finite algebraic sanity checks, not a formal verification of the manuscript",
        "not_checked": ["arbitrary reverse-well-ordered supports", "infinite Hahn summation",
                        "Hartogs/class arguments", "published primality theorem",
                        "Scott quotient construction", "Lean proofs"]
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks.json"))
    args = parser.parse_args()
    report = run_checks()
    try:
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    except OSError as exc:
        print(f"Could not write report: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
