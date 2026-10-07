#!/usr/bin/env python3
"""Exact supplementary checks for the bounded centered U^2 theorem.

Run from any working directory. No numerical FFT is used: every correlation
and inequality is reduced to integer arithmetic. These finite checks supplement
the general proofs in the manuscript, rather than proving untested cases.
"""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def group_table(moduli):
    elements = list(product(*(range(n) for n in moduli)))
    index = {x: j for j, x in enumerate(elements)}
    add = [[index[tuple((a + b) % n for a, b, n in zip(x, y, moduli))]
            for y in elements] for x in elements]
    return elements, add


def check_group(moduli):
    elements, add = group_table(moduli)
    n = len(elements)
    count = 0
    maximum_numerator = 0
    equality_cases = 0
    for f in product((-1, 0, 1), repeat=n):
        if sum(f) != 0:
            continue
        corr = [sum(f[x] * f[add[x][h]] for x in range(n))
                for h in range(n)]
        squared_sum = sum(a * a for a in corr)
        slacks = [(n + corr[add[h][h]]) ** 2 - 4 * corr[h] ** 2
                  for h in range(n)]
        assert min(slacks) >= 0
        assert sum(slacks) == n ** 3 - 3 * squared_sum
        assert 3 * squared_sum <= n ** 3 - 4 * n + 3
        if 3 * squared_sum == n ** 3 - 4 * n + 3:
            equality_cases += 1
        maximum_numerator = max(maximum_numerator, squared_sum)
        count += 1
    return {
        "moduli": moduli,
        "centered_ternary_functions_checked": count,
        "maximum_in_tested_class": str(Fraction(maximum_numerator, n ** 3)),
        "sharp_universal_order_bound": str(Fraction(n ** 3 - 4 * n + 3, 3 * n ** 3)),
        "equality_cases_in_tested_class": equality_cases,
    }


def check_cyclic_extremizers():
    cases = []
    for n in range(3, 202, 2):
        m = (n - 1) // 2
        f = [0] + [1] * m + [-1] * m
        corr = [sum(f[x] * f[(x + h) % n] for x in range(n))
                for h in range(n)]
        assert corr[0] == n - 1
        for h in range(1, m + 1):
            assert corr[h] == n - 4 * h
            assert corr[-h] == corr[h]
        value = Fraction(sum(a * a for a in corr), n ** 3)
        target = Fraction(1, 3) - Fraction(4, 3 * n * n) + Fraction(1, n ** 3)
        assert value == target
        cases.append({"N": n, "U2_fourth": str(value)})
    return cases


def main():
    scalar_checks = 0
    for u, v, w in product(range(-4, 5), repeat=3):
        assert u * v + v * w - u * w <= 16
        assert -u * v - v * w - u * w <= 16
        scalar_checks += 1
    groups = [check_group(moduli) for moduli in ([3], [5], [7], [9], [3, 3])]
    cycles = check_cyclic_extremizers()
    result = {
        "status": "all exact supplementary checks passed",
        "scope": "Finite tested cases only; general statements are proved analytically in the article.",
        "scalar_grid_triples": scalar_checks,
        "groups": groups,
        "total_centered_ternary_functions_checked": sum(g["centered_ternary_functions_checked"] for g in groups),
        "cyclic_extremizers_checked": len(cycles),
        "cyclic_examples": cycles,
    }
    out = Path(__file__).resolve().parents[1] / "data" / "verify_bounded_norm.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("groups", "cyclic_examples")}, indent=2))


if __name__ == "__main__":
    main()
