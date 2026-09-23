#!/usr/bin/env python3
"""Exact finite checks accompanying Drazin Halos.

Python 3.10+; standard library only. No files are written without --output.
These finite calculations do NOT prove arbitrary-support or infinite-dimensional
claims. Assertion counts are individual calls to check(), not matrix entries.
"""
from __future__ import annotations

import argparse
import json
import platform
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
from typing import Dict, Tuple

Matrix = Tuple[Tuple[F, ...], ...]
ScalarSeries = Dict[int, F]
MatrixSeries = Dict[int, Matrix]
COUNTS: Counter = Counter()


def check(condition: bool, category: str, detail: str) -> None:
    if not condition:
        raise AssertionError(f"{category}: {detail}")
    COUNTS[category] += 1


def zero(n: int) -> Matrix:
    return tuple(tuple(F(0) for _ in range(n)) for _ in range(n))


def eye(n: int) -> Matrix:
    return tuple(tuple(F(i == j) for j in range(n)) for i in range(n))


def add(a: Matrix, b: Matrix) -> Matrix:
    return tuple(tuple(x + y for x, y in zip(ar, br)) for ar, br in zip(a, b))


def scale(c: F, a: Matrix) -> Matrix:
    return tuple(tuple(c * x for x in row) for row in a)


def mul(a: Matrix, b: Matrix) -> Matrix:
    n = len(a)
    return tuple(tuple(sum((a[i][k] * b[k][j] for k in range(n)), F(0))
                       for j in range(n)) for i in range(n))


def power(a: Matrix, k: int) -> Matrix:
    result = eye(len(a))
    for _ in range(k):
        result = mul(result, a)
    return result


def inv(a: Matrix) -> Matrix:
    n = len(a)
    aug = [list(a[i]) + list(eye(n)[i]) for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if aug[i][j]), None)
        if pivot is None:
            raise ValueError("Matrix is singular")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        c = aug[j][j]
        aug[j] = [v / c for v in aug[j]]
        for i in range(n):
            if i != j:
                c = aug[i][j]
                aug[i] = [x - c * y for x, y in zip(aug[i], aug[j])]
    return tuple(tuple(row[n:]) for row in aug)


def jordan(n: int) -> Matrix:
    return tuple(tuple(F(j == i + 1) for j in range(n)) for i in range(n))


def block(a: Matrix, b: Matrix) -> Matrix:
    n, m = len(a), len(b)
    return tuple(tuple(a[i][j] if i < n and j < n else
                       b[i-n][j-n] if i >= n and j >= n else F(0)
                       for j in range(n+m)) for i in range(n+m))


def clean_m(a: MatrixSeries) -> MatrixSeries:
    return {e: c for e, c in a.items() if any(any(row) for row in c)}


def madd(a: MatrixSeries, b: MatrixSeries) -> MatrixSeries:
    out = dict(a)
    for e, c in b.items():
        out[e] = add(out.get(e, zero(len(c))), c)
    return clean_m(out)


def mmul(a: MatrixSeries, b: MatrixSeries, top: int | None = None) -> MatrixSeries:
    out: MatrixSeries = {}
    for i, x in a.items():
        for j, y in b.items():
            if top is None or i+j <= top:
                out[i+j] = add(out.get(i+j, zero(len(x))), mul(x, y))
    return clean_m(out)


def sadd(a: ScalarSeries, b: ScalarSeries) -> ScalarSeries:
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, F(0)) + c
    return {e: c for e, c in out.items() if c}


def smul(a: ScalarSeries, b: ScalarSeries, top: int) -> ScalarSeries:
    out: ScalarSeries = {}
    for i, x in a.items():
        for j, y in b.items():
            if i+j <= top:
                out[i+j] = out.get(i+j, F(0)) + x*y
    return {e: c for e, c in out.items() if c}


def spow(a: ScalarSeries, k: int, top: int) -> ScalarSeries:
    result = {0: F(1)}
    for _ in range(k):
        result = smul(result, a, top)
    return result


def binomial(h: ScalarSeries, q: F, top: int) -> ScalarSeries:
    if not h:
        return {0: F(1)} if top >= 0 else {}
    if min(h) <= 0:
        raise ValueError("Binomial correction must have positive order")
    result: ScalarSeries = {0: F(1)} if top >= 0 else {}
    term, coefficient = {0: F(1)}, F(1)
    for n in range(1, top // min(h) + 1):
        term = smul(term, h, top)
        coefficient *= (q - n + 1) / n
        result = sadd(result, {e: coefficient*c for e, c in term.items()})
    return result


def compose(a: ScalarSeries, b: ScalarSeries, top: int) -> ScalarSeries:
    if a and min(a) < 0:
        raise ValueError("Composition expects a power series")
    if b and min(b) <= 0:
        raise ValueError("Inner series must have zero constant term")
    out: ScalarSeries = {}
    for k, c in a.items():
        if k <= top:
            out = sadd(out, {e: c*v for e, v in spow(b, k, top).items()})
    return out


def formal_inverse(h: ScalarSeries, top: int) -> ScalarSeries:
    c = h.get(1, F(0))
    if not c:
        raise ValueError("Nonzero linear coefficient required")
    j: ScalarSeries = {1: 1/c}
    for n in range(2, top+1):
        v = compose(h, j, n).get(n, F(0))
        if v:
            j[n] = -v/c
    return j


def phi(a: ScalarSeries, h: ScalarSeries, top: int) -> ScalarSeries:
    """Truncated substitution u -> u(1+h); integer Laurent exponents."""
    out: ScalarSeries = {}
    for gamma, c in a.items():
        correction = binomial(h, F(gamma), top-gamma)
        out = sadd(out, {gamma+e: c*v for e, v in correction.items()
                         if gamma+e <= top})
    return out


def theta(a: ScalarSeries, h: ScalarSeries, top: int) -> ScalarSeries:
    """The finite-to-order version of sum (-Delta)^n, Delta=phi-id."""
    out, term = {}, dict(a)
    max_steps = 2 + (top-min(a)) // min(h) if a else 0
    for _ in range(max_steps):
        out = sadd(out, term)
        term = sadd(term, {e: -c for e, c in phi(term, h, top).items()})
        if not term:
            return out
    raise AssertionError("Contraction did not terminate at the expected order")


def run() -> dict:
    category = "pure_nilpotent_inverse"
    for n in range(1, 11):
        j, identity = jordan(n), eye(n)
        pencil = clean_m({0: j, 1: scale(F(-1), identity)})
        r = clean_m({-k-1: scale(F(-1), power(j, k)) for k in range(n)})
        check(mmul(pencil, r) == {0: identity}, category, f"left n={n}")
        check(mmul(r, pencil) == {0: identity}, category, f"right n={n}")
        check(min(r) == -n, category, f"pole n={n}")

    category = "mixed_drazin_and_truncated_residual"
    c = ((F(2), F(1)), (F(0), F(3)))
    for nu in range(1, 8):
        n = nu+2
        u = add(eye(n), scale(F(1, 2), jordan(n)))
        ui = inv(u)
        s = mul(mul(u, block(jordan(nu), c)), ui)
        d = mul(mul(u, block(zero(nu), inv(c))), ui)
        p = add(eye(n), scale(F(-1), mul(s, d)))
        check(mul(s, d) == mul(d, s), category, f"commutation nu={nu}")
        check(mul(mul(d, s), d) == d, category, f"reflexive nu={nu}")
        check(mul(power(s, nu+1), d) == power(s, nu), category, f"index nu={nu}")
        check(mul(power(s, nu-1), p) != zero(n), category, f"least index nu={nu}")
        pencil = {0: s, 1: scale(F(-1), eye(n))}
        negative = {-j-1: scale(F(-1), mul(power(s, j), p)) for j in range(nu)}
        for top in range(7):
            r = madd(negative, {j: power(d, j+1) for j in range(top+1)})
            target = clean_m({0: eye(n), top+1: scale(F(-1), power(d, top+1))})
            check(mmul(pencil, r) == target, category, f"left nu={nu} top={top}")
            check(mmul(r, pencil) == target, category, f"right nu={nu} top={top}")
            check(min(r) == -nu, category, f"valuation nu={nu} top={top}")

    category = "ramified_nilpotent_pole_order"
    for nu in range(1, 16):
        j = jordan(nu)
        unit = add(add(eye(nu), scale(F(2), j)), power(j, 2))
        for r in range(1, 8):
            a = mul(power(j, r), unit)
            k = (nu+r-1)//r
            check(power(a, k) == zero(nu), category, f"vanishing nu={nu} r={r}")
            check(power(a, k-1) != zero(nu), category, f"minimal nu={nu} r={r}")

    category = "formal_ramified_germs"
    top = 14
    base = {1: F(1), 2: F(2)}
    for r in range(1, 7):
        h = {e+1: c for e, c in binomial(base, F(1, r), top-1).items()}
        expected = {r: F(1), r+1: F(1), r+2: F(2)}
        expected = {e: c for e, c in expected.items() if e <= top}
        check(spow(h, r, top) == expected, category, f"power identity r={r}")
        j = formal_inverse(h, top)
        check(compose(h, j, top) == {1: F(1)}, category, f"h o j r={r}")
        check(compose(j, h, top) == {1: F(1)}, category, f"j o h r={r}")

    category = "nonmonomial_nilpotent_inverse"
    top, correction = 16, {2: F(1), 5: F(1)}
    epsilon = {1: F(1), 3: F(1), 6: F(1)}
    for nu in range(1, 9):
        j, identity = jordan(nu), eye(nu)
        pencil = madd({0: j}, {e: scale(-c, identity) for e, c in epsilon.items()})
        r: MatrixSeries = {}
        for k in range(1, nu+1):
            term = binomial(correction, F(-k), top+k)
            r = madd(r, {e-k: scale(-c, power(j, k-1)) for e, c in term.items()})
        check(mmul(pencil, r, top) == {0: identity}, category, f"left nu={nu}")
        check(mmul(r, pencil, top) == {0: identity}, category, f"right nu={nu}")
        check(min(r) == -nu and r[-nu] == scale(F(-1), power(j, nu-1)),
              category, f"leading term nu={nu}")

    category = "truncated_straightening_automorphism"
    for top in (9, 13, 18):
        for h in ({1: F(2)}, {2: F(1), 5: F(1)}, {3: F(-2), 4: F(3)}):
            x = {-5: F(2), -1: F(-3), 0: F(7), 2: F(1, 2), 7: F(5)}
            check(phi(theta(x, h, top), h, top) == x, category, f"PhiTheta top={top}")
            check(theta(phi(x, h, top), h, top) == x, category, f"ThetaPhi top={top}")
            a, b = {0: F(1), 1: F(2), 3: F(-1)}, {1: F(2), 4: F(3)}
            check(phi(smul(a, b, top), h, top) ==
                  smul(phi(a, h, top), phi(b, h, top), top),
                  category, f"multiplication top={top}")

    return {
        "status": "passed",
        "arithmetic": "exact fractions.Fraction; no floating-point comparisons",
        "python_version": platform.python_version(),
        "assertions_total": sum(COUNTS.values()),
        "assertions_by_category": dict(sorted(COUNTS.items())),
        "formal_germ_max_degree": 14,
        "straightening_max_degree": 18,
        "nonmonomial_inverse_max_degree": 16,
        "limits": [
            "Finite instances only; no proof of arbitrary Hahn summability.",
            "No infinite-dimensional operator was approximated as a proof.",
            "No Lean formal verification or independent mathematical review."
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write JSON here; omit for stdout only")
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    print(text, end="")
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")


if __name__ == "__main__":
    main()
