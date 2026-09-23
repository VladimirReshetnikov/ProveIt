#!/usr/bin/env python3
"""Exact finite checks accompanying Automatic Summability from Omnific Arithmetic.

These checks validate finite identities and examples, not the infinite theorems.
Python 3.9+; standard library only. Run from any working directory.
"""
from __future__ import annotations

import json
import random
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

Q = Fraction
Series = Dict[int, Fraction]


def binomial_coefficients(a: Fraction, degree: int) -> List[Fraction]:
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    result = [Q(1)]
    for n in range(1, degree + 1):
        result.append(result[-1] * (a - (n - 1)) / n)
    return result


def convolution(a: List[Fraction], b: List[Fraction], degree: int) -> List[Fraction]:
    return [sum((a[j] * b[n - j] for j in range(n + 1)), Q(0))
            for n in range(degree + 1)]


def pairing(x: Series, y: Series) -> Fraction:
    return sum((c * y.get(-g, Q(0)) for g, c in x.items()), Q(0))


def binomial_checks() -> dict:
    degree = 20
    parameters = sorted({Q(a, b) for a in range(-5, 6) for b in range(1, 5)})
    pairs = 0
    for a in parameters:
        ca = binomial_coefficients(a, degree)
        inv = convolution(ca, binomial_coefficients(-a, degree), degree)
        assert inv == [Q(1)] + [Q(0)] * degree, ("inverse", a)
        for b in parameters:
            actual = convolution(ca, binomial_coefficients(b, degree), degree)
            expected = binomial_coefficients(a + b, degree)
            assert actual == expected, ("multiplication", a, b)
            pairs += 1
    assert binomial_coefficients(Q(-1), degree) == [Q((-1) ** n) for n in range(degree + 1)]
    return {"status": "passed", "degree": degree,
            "parameter_count": len(parameters), "multiplication_cases": pairs,
            "inverse_cases": len(parameters),
            "scope": "Formal binomial identities only through the stated finite degree."}


def matching_checks() -> dict:
    # Every row is nonempty; row n meets columns n, n+1, and n+3.
    # An infinite matrix with this pattern is locally finite. Here we check a prefix.
    size = 256
    rows = {n: {n: Q(1), n + 1: Q(-2), n + 3: Q(3)} for n in range(size)}
    chosen: List[Tuple[int, int]] = []
    forbidden_columns = set()
    for n in range(size):
        support = set(rows[n])
        if support.isdisjoint(forbidden_columns):
            col = min(support)
            chosen.append((n, col))
            forbidden_columns.update(support)
    assert len(chosen) > 1
    for j, (n, col) in enumerate(chosen):
        assert rows[n][col] != 0
        for ell, (_, other_col) in enumerate(chosen):
            if j != ell:
                assert rows[n].get(other_col, Q(0)) == 0
    # g_n=-n, hence the matching detector is sum t^n over selected rows.
    detector: Series = {n: Q(1) for n, _ in chosen}
    for n, col in chosen:
        x_col = {-r: row[col] for r, row in rows.items() if col in row}
        assert pairing(x_col, detector) == rows[n][col]
    return {"status": "passed", "matrix_rows": size,
            "matching_size": len(chosen), "first_pairs": chosen[:8],
            "scope": "Induced matching and detector coefficients on a finite matrix prefix."}


def adjoint_checks() -> dict:
    rng = random.Random(20260923)
    source = list(range(-6, 7))
    target = list(range(-4, 5))
    # T[(h,g)] is the coefficient of t^h in T(t^g).
    matrix = {(h, g): Q(rng.randrange(-4, 5)) for h in target for g in source}
    trials = 100
    for _ in range(trials):
        x = {g: Q(rng.randrange(-5, 6), rng.randrange(1, 5)) for g in source}
        y = {h: Q(rng.randrange(-5, 6), rng.randrange(1, 5)) for h in target}
        tx = {h: sum((matrix[h, g] * x[g] for g in source), Q(0)) for h in target}
        adj_y = {g: sum((matrix[-h, -g] * y[h] for h in target), Q(0)) for g in source}
        assert pairing(tx, y) == pairing(x, adj_y)
    return {"status": "passed", "trials": trials,
            "source_dimension": len(source), "target_dimension": len(target),
            "scope": "Exact finite sign-reversed transpose identity, not an infinite support test."}


def cancellation_checks() -> dict:
    cases = []
    for size in (1, 2, 5, 16, 64):
        detector = {n: Q(1) for n in range(1, size + 1)}
        values = []
        for n in range(1, size + 1):
            values.extend([pairing({-n: Q(1)}, detector), pairing({-n: Q(-1)}, detector)])
        assert values == [Q(1), Q(-1)] * size
        assert sum(values, Q(0)) == 0 and all(v != 0 for v in values)
        cases.append({"pairs": size, "nonzero_pairings": len(values), "total": 0})
    return {"status": "passed", "cases": cases,
            "scope": "Finite-prefix cancellation checks; the infinite obstruction is proved in the article."}


def main() -> None:
    report = {"title": "Automatic Summability from Omnific Arithmetic",
              "arithmetic": "Exact fractions; no floating point",
              "infinite_theorems_formally_verified": False,
              "binomial": binomial_checks(), "matching": matching_checks(),
              "adjoint": adjoint_checks(), "cancellation": cancellation_checks()}
    report["all_finite_checks_passed"] = True
    destination = Path(__file__).resolve().parents[1] / "data" / "verification.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
