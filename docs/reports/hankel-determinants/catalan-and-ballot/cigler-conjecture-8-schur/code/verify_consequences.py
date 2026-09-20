#!/usr/bin/env python3
"""Supplementary exact checks of edge, recurrence and asymptotic formulas.

Run after or independently of verify.py. Python standard library only.
The first asymptotic constant is checked as a symbolic leading coefficient
in n (via exact finite differences), not by floating-point approximation.
"""
from __future__ import annotations
import json
from math import comb, factorial
from pathlib import Path
from verify import (Poly, ZERO, ONE, add, sub, mul, scale, shift, require,
                    hankel, partition_sum, numerator_blocks)


def recurrence_operator(k: int) -> list[Poly]:
    """Coefficients in ascending powers of E, each a polynomial in t."""
    op = [ONE]
    for j in range(k + 1):
        for _ in range(2 * j * (k - j) + 1):
            nxt = [ZERO] * (len(op) + 1)
            for r, coefficient in enumerate(op):
                nxt[r] = sub(nxt[r], shift(coefficient, j))
                nxt[r + 1] = add(nxt[r + 1], coefficient)
            op = nxt
    return op


def main() -> None:
    edge_count = 0
    for k in range(1, 7):
        for n in range(11):
            p = partition_sum(k, n)
            actual = p[n + 1] if n + 1 < len(p) else 0
            expected = comb(k * k + n, n + 1) - comb(n + k, k - 1)**2
            require(actual == expected, f"next-edge formula failed at {k=}, {n=}")
            edge_count += 1

    leading_count = 0
    for k in range(1, 7):
        d = 2 * k - 2
        values = [numerator_blocks(k, n)[1] for n in range(d + 1)]
        while len(values) > 1:
            values = [sub(values[r + 1], values[r])
                      for r in range(len(values) - 1)]
        # d-th forward difference equals d! times the coefficient of n^d.
        left = scale(values[0], factorial(k - 1)**2)
        right = scale(tuple((-1)**r * comb(d, r) for r in range(d + 1)),
                      factorial(d))
        require(left == right, f"asymptotic leading coefficient failed at {k=}")
        leading_count += 1

    recurrence_checks = []
    for k in range(1, 4):
        op = recurrence_operator(k)
        order = len(op) - 1
        require(order == (k + 1) * (k * k - k + 3) // 3,
                "recurrence order formula failed")
        rows = [hankel(k, n) for n in range(order + 3)]
        for n in range(3):
            residual = ZERO
            for r, coefficient in enumerate(op):
                residual = add(residual, mul(coefficient, rows[n + r]))
            require(residual == ZERO, f"recurrence failed at {k=}, {n=}")
        recurrence_checks.append({"k": k, "order": order,
                                  "initial_window_starts": [0, 1, 2],
                                  "largest_raw_hankel_order": order + 2})
    report = {
        "status": "PASS",
        "first_post_stable_edge_checks": edge_count,
        "symbolic_asymptotic_leading_coefficient_checks": leading_count,
        "recurrence_checks": recurrence_checks,
        "recurrence_windows_total": 9,
        "disagreements": 0,
        "scope": "finite exact checks; the all-parameter proofs are in article.tex"
    }
    target = Path(__file__).resolve().parent.parent / "results" / "consequences.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
