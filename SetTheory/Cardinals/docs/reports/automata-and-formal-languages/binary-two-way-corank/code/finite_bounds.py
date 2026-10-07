#!/usr/bin/env python3
"""Exact finite corank recurrence and explicit four-label obstruction.

Only the Python standard library is required. The recurrence in the article
is evaluated with integer division. The closed-form comparison uses Fraction.
No finite calculation is used as a premise for the infinite theorem.
"""
from __future__ import annotations
import argparse
import csv
from fractions import Fraction
import json
from pathlib import Path
from brauer_audit import multiply


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def ceil_fraction(value: Fraction) -> int:
    return (value.numerator + value.denominator - 1) // value.denominator


def finite_bounds(max_h: int) -> tuple[list[int], list[int | None]]:
    require(max_h >= 2, "max_h must be at least 2")
    bounds = [0] * (max_h + 1)
    choices: list[int | None] = [None] * (max_h + 1)
    bounds[2] = 1
    for h in range(3, max_h + 1):
        best = 1
        for total in range(2, h):
            product = (total * total) // 4
            numerator = product * bounds[h - total + 1]
            candidate = (numerator + total - 1) // total
            if candidate > best:
                best = candidate
                choices[h] = total
        bounds[h] = best
    return bounds, choices


def obstruction() -> dict[str, object]:
    a = (1, 0, 4, 7, 2, 6, 5, 3)
    b = (1, 0, 6, 4, 3, 7, 2, 5)
    require(multiply(a, a) == a, "a is not idempotent")
    require(multiply(b, b) == b, "b is not idempotent")
    require(multiply(a, b) == b, "ab is not b")
    require(multiply(b, a) == a, "ba is not a")
    require(sum(a[i] >= 4 for i in range(4)) == 2
            and sum(b[i] >= 4 for i in range(4)) == 2, "incorrect ranks")
    return {"degree": 4, "a": a, "b": b,
            "multiplication": {"aa": "a", "ab": "b", "ba": "a", "bb": "b"},
            "union_cap_edges": [[0, 1], [0, 1], [1, 2], [1, 3]],
            "connected_union_parity_rank_bound": 0,
            "actual_minimum_generated_rank": 2}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-h", type=int, default=256)
    parser.add_argument("--output", type=Path,
                        default=Path("certificates/finite_bounds.json"))
    parser.add_argument("--csv", type=Path,
                        default=Path("certificates/finite_bounds.csv"))
    args = parser.parse_args()
    bounds, choices = finite_bounds(args.max_h)
    rows = []
    for h in range(2, args.max_h + 1):
        closed = 2 * Fraction(5, 2) ** ((h - 2) // 9)
        require(Fraction(2 * bounds[h]) >= closed,
                f"finite bound weaker than valid closed recurrence at h={h}")
        row = {"h": h, "source_states": 6 * h + 2,
               "old_degree_bound": 2 ** ((h - 2) // 31),
               "closed_degree_ceiling": ceil_fraction(closed),
               "D": bounds[h], "finite_degree_bound": 2 * bounds[h],
               "binary_target_state_bound": max(1, (bounds[h] + 2) // 4),
               "chosen_arm_sum": choices[h]}
        rows.append(row)
    result = {"status": "pass", "arithmetic": "exact integers and rational fractions",
              "maximum_h": args.max_h, "recurrence_rows": rows,
              "union_graph_obstruction": obstruction()}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.csv.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    with args.csv.open("w", newline="", encoding="utf-8") as target:
        writer = csv.DictWriter(target, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({"status": "pass", "maximum_h": args.max_h,
                      "output": str(args.output), "csv": str(args.csv)}))


if __name__ == "__main__":
    main()
