#!/usr/bin/env python3
"""Exact rational demonstrations for the measure section.

These finite checks validate implementations and displayed constants.
They do not prove the universal theorems or compile object-iPRA derivations.
Only Python's standard library is required.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import json
from pathlib import Path


@dataclass(frozen=True)
class Step:
    level: int
    values: tuple[F, ...]

    def __post_init__(self) -> None:
        if self.level < 0 or len(self.values) != 2 ** self.level:
            raise ValueError("Malformed dyadic step")

    def refine(self, new_level: int) -> Step:
        if new_level < self.level:
            raise ValueError("Refinement level must not decrease")
        repeat = 2 ** (new_level - self.level)
        return Step(new_level, tuple(x for x in self.values for _ in range(repeat)))

    def integral(self) -> F:
        return sum(self.values, F(0)) / len(self.values)

    def norm1(self) -> F:
        return sum(map(abs, self.values), F(0)) / len(self.values)

    def energy(self) -> F:
        return sum((x * x for x in self.values), F(0)) / len(self.values)

    def conditional(self, level: int) -> Step:
        if level >= self.level:
            return self.refine(level)
        block = 2 ** (self.level - level)
        return Step(
            level,
            tuple(
                sum(self.values[i * block : (i + 1) * block], F(0)) / block
                for i in range(2 ** level)
            ),
        )

    def excess(self, K: F) -> F:
        return sum((max(abs(x) - K, F(0)) for x in self.values), F(0)) / len(
            self.values
        )


def common(a: Step, b: Step) -> tuple[Step, Step]:
    level = max(a.level, b.level)
    return a.refine(level), b.refine(level)


def subtract(a: Step, b: Step) -> Step:
    a, b = common(a, b)
    return Step(a.level, tuple(x - y for x, y in zip(a.values, b.values)))


def distance(a: Step, b: Step) -> F:
    return subtract(a, b).norm1()


def d0(a: Step, b: Step) -> F:
    a, b = common(a, b)
    return sum((min(F(1), abs(x - y)) for x, y in zip(a.values, b.values)), F(0)) / len(
        a.values
    )


def affine_masses(n: int) -> tuple[F, ...]:
    def nu(a: F, b: F) -> F:
        return F(2, 3) * (b - a) + F(1, 3) * (b * b - a * a)

    return tuple(nu(F(i, 2 ** n), F(i + 1, 2 ** n)) for i in range(2 ** n))


def affine_density(n: int) -> Step:
    return Step(n, tuple(2 ** n * v for v in affine_masses(n)))


def affine_energy(n: int) -> F:
    # Proved independently in the report, and checked against array sums below.
    return F(28, 27) - F(1, 27 * 4 ** n)


def finite_energy_window(p: int, challenge, energy, cap: int) -> dict:
    """Explicit bounded search; challenge and energy are fixed callables."""
    bound = cap * 4 ** p + 1
    t = 0
    threshold = F(1, 4 ** p)
    for j in range(bound):
        nxt = max(t, challenge(t))
        gap = energy(nxt) - energy(t)
        if gap <= threshold:
            return {"j": j, "N": t, "end": nxt, "bound": bound, "gap": str(gap)}
        t = nxt
    raise AssertionError("Energy cap did not force a good window")


def ceil_log2_rational(K: F) -> int:
    if K < 1:
        raise ValueError("K must be at least one")
    # Explicit primitive recursive bound, rather than an unbounded loop.
    for h in range(abs(K.numerator) + 2):
        if K <= 2 ** h:
            return h
    raise AssertionError("Elementary logarithm search bound failed")


def main() -> dict:
    counts: dict[str, int] = {}

    def check(group: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(f"Failed check in {group}")
        counts[group] = counts.get(group, 0) + 1

    # The exact counterexample pinpoints the repaired source statement.
    x, y, K = F(2), F(-1), F(1)
    old_rhs = (
        (abs(x - y) if abs(x) <= K and abs(y) <= K else 0)
        + (abs(x) if abs(x) > K else 0)
        + (abs(y) if abs(y) > K else 0)
    )
    check("source_correction", abs(x - y) == 3 and old_rhs == 2)

    # Selected scalar cases at the clipping boundary and away from it.
    grid = [F(-5), F(-2), F(-1), F(-1, 2), F(0), F(1, 2), F(1), F(2), F(5)]
    for K in [F(1), F(3, 2), F(2)]:
        for x in grid:
            check("excess_square", 4 * K * max(abs(x) - K, F(0)) <= x * x)
            for y in grid:
                rhs = (
                    2 * K * min(F(1), abs(x - y))
                    + max(abs(x) - K, F(0))
                    + max(abs(y) - K, F(0))
                )
                check("stable_clipping", abs(x - y) <= rhs)

    # Exact rational refinement and conditional averaging.
    steps = [
        Step(r, tuple(F((13 * i + 7 * r) % 23 - 11, 3 + i % 5) for i in range(2 ** r)))
        for r in range(7)
    ]
    for a in steps:
        for n in range(7):
            ea = a.conditional(n)
            check("conditional_integral", ea.integral() == a.integral())
            check("conditional_contraction", ea.norm1() <= a.norm1())
            for m in range(7):
                left = ea.conditional(m)
                right = a.conditional(min(n, m))
                check("tower", distance(left, right) == 0)
        check("finite_cauchy_schwarz", a.norm1() ** 2 <= a.energy())

    # Rectangular Fubini and the contraction of a partial average.
    for r in range(4):
        for s in range(4):
            rows, cols = 2 ** r, 2 ** s
            a = [[F((13 * i - 7 * j) % 19 - 9, 3) for j in range(cols)] for i in range(rows)]
            b = [[a[i][j] + F((i + 2 * j) % 7 - 3, 5) for j in range(cols)] for i in range(rows)]
            total = sum((v for row in a for v in row), F(0)) / (rows * cols)
            row_a = [sum(row, F(0)) / cols for row in a]
            col_a = [sum((a[i][j] for i in range(rows)), F(0)) / rows for j in range(cols)]
            check("fubini", total == sum(row_a, F(0)) / rows)
            check("fubini", total == sum(col_a, F(0)) / cols)
            row_b = [sum(row, F(0)) / cols for row in b]
            partial_dist = sum((abs(x - y) for x, y in zip(row_a, row_b)), F(0)) / rows
            full_dist = sum(
                (abs(a[i][j] - b[i][j]) for i in range(rows) for j in range(cols)), F(0)
            ) / (rows * cols)
            check("partial_average_contraction", partial_dist <= full_dist)

    # Recover a normalized density entirely from coherent interval masses.
    densities = [affine_density(n) for n in range(10)]
    for n, dn in enumerate(densities):
        check("rn_normalization", dn.integral() == 1)
        check("rn_positivity", all(x >= 0 for x in dn.values))
        check("rn_energy_formula", dn.energy() == affine_energy(n))
        check("rn_energy_tail", F(28, 27) - dn.energy() == F(1, 27 * 4 ** n))
        if n + 1 < len(densities):
            fine = affine_masses(n + 1)
            coarse = affine_masses(n)
            for i, v in enumerate(coarse):
                check("mass_coherence", v == fine[2 * i] + fine[2 * i + 1])
                sibling_gap = abs(densities[n + 1].values[2 * i] - densities[n + 1].values[2 * i + 1])
                check("sibling_rate", sibling_gap == F(1, 3 * 2 ** n))
        for m in range(n, len(densities)):
            dm = densities[m]
            gap = dm.energy() - dn.energy()
            check("rn_orthogonal_energy", subtract(dm, dn).energy() == gap)
            check("rn_l1_energy", distance(dm, dn) ** 2 <= gap)
            check("rn_regular_name", distance(dm, dn) <= F(1, 2 ** n))
            check("rn_coarse_average", distance(dm.conditional(n), dn) == 0)

    # The quantitative Vitali schedule has the advertised three-way budget.
    vitali_budgets = []
    for p in range(9):
        cutoff = F(3 * 2 ** (p + 2))  # a valid example U(p+2) from an L2 cap
        h = ceil_log2_rational(cutoff)
        q = p + 3 + h
        metric_term = 2 * cutoff * F(1, 2 ** q)
        each_tail = F(1, 2 ** (p + 2))
        total = metric_term + 2 * each_tail
        check("vitali_budget", metric_term <= F(1, 2 ** (p + 2)))
        check("vitali_budget", total <= F(3, 4 * 2 ** p))
        vitali_budgets.append({"p": p, "K": str(cutoff), "h": h, "q": q, "total_bound": str(total)})

    # Full bounded search, with energies evaluated algebraically.
    windows = []
    for p in range(7):
        result = finite_energy_window(p, lambda n: n + 2, affine_energy, 2)
        check("metastability_search", result["j"] < result["bound"])
        lo, hi = result["N"], result["end"]
        for m in range(lo, hi + 1):
            for n in range(lo, hi + 1):
                gap = abs(affine_energy(m) - affine_energy(n))
                check("metastability_interior", gap <= F(1, 4 ** p))
        result["p"] = p
        windows.append(result)

    # A delayed Rademacher jump shows why a single observed quiet window
    # does not constitute an eventual convergence rate.
    delayed = []
    for halt_time in [0, 1, 3, 6]:
        before = Step(halt_time, tuple(F(1) for _ in range(2 ** halt_time)))
        after = Step(halt_time + 1, tuple(F(3, 2) if i % 2 == 0 else F(1, 2) for i in range(2 ** (halt_time + 1))))
        check("delayed_jump", distance(before, after) == F(1, 2))
        check("delayed_jump", before.energy() == 1 and after.energy() == F(5, 4))
        check("delayed_jump", distance(after.conditional(halt_time), before) == 0)
        delayed.append({"jump_level": halt_time + 1, "L1_jump": "1/2", "energy_cap": "5/4"})

    return {
        "status": "passed",
        "arithmetic": "exact fractions; no floating-point pass/fail tests",
        "counts": counts,
        "total_assertions": sum(counts.values()),
        "source_counterexample": {"x": "2", "y": "-1", "K": "1", "lhs": "3", "old_rhs": "2"},
        "affine_density": {
            "formula": "2(1+t)/3",
            "mass_formula": "2(b-a)/3+(b^2-a^2)/3",
            "energy_formula": "28/27-4^(-n)/27",
            "levels_checked": len(densities),
        },
        "vitali_budgets": vitali_budgets,
        "metastability_windows": windows,
        "delayed_jumps": delayed,
        "scope": "Finite implementation checks; not a universal theorem proof or an object-iPRA derivation.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = main()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print(rendered)
