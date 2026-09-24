#!/usr/bin/env python3
"""Exact, finite checks for the accompanying set-theoretic research note.

No external packages are required. These checks do NOT construct a free
ultrafilter, establish the Baire-category argument, or certify an infinite
mathematical theorem. They test the explicit geometry and finite fusion
invariants used in the written proofs. Run with Python 3.10 or later.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import platform
import random
import sys
from pathlib import Path
from typing import Any


class Audit:
    def __init__(self) -> None:
        self.counts: dict[str, int] = {}

    def check(self, condition: bool, category: str, detail: Any = None) -> None:
        # Deliberately not an assert: checks remain active under python -O.
        self.counts[category] = self.counts.get(category, 0) + 1
        if not condition:
            raise AssertionError(f"{category}: {detail!r}")


def boundary(n: int) -> int:
    if n < 0:
        raise ValueError("The level must be nonnegative")
    return (4**n - 1) // 3 + 2 * (2**n - 1)


def node(n: int, word_value: int) -> int:
    if n < 0 or not 0 <= word_value < 2**n:
        raise ValueError("Invalid binary word")
    return boundary(n) + 2**n * (1 + word_value)


def prefix_branch(word: int, depth: int) -> frozenset[int]:
    if not 0 <= word < 2**depth:
        raise ValueError("Invalid branch prefix")
    return frozenset(node(n, word >> (depth - n)) for n in range(depth + 1))


def shifts(count: int) -> list[int]:
    ans = [0]
    for n in range(1, count):
        ans.append((n + 1) // 2 if n % 2 else -(n // 2))
    return ans


def auxiliary_boundary(n: int) -> int:
    return n * (n + 5) // 2


def auxiliary_block(x: int) -> int:
    if x < 0:
        raise ValueError("Point outside omega")
    n = max(0, (math.isqrt(25 + 8 * x) - 5) // 2)
    while auxiliary_boundary(n + 1) <= x:
        n += 1
    while auxiliary_boundary(n) > x:
        n -= 1
    return n


def interval_support(interval: tuple[int, int], offset: int) -> frozenset[int]:
    lo, hi = interval
    lo, hi = max(0, lo + offset), hi + offset
    if hi <= lo:
        return frozenset()
    return frozenset(range(auxiliary_block(lo), auxiliary_block(hi - 1) + 1))


def test_fusion(audit: Audit, seed: int, stages: int) -> dict[str, Any]:
    """Test the fusion lemma using blocks of lengths 3,4,5,... ."""
    rng = random.Random(seed)
    offsets = shifts(stages)
    q_intervals: list[tuple[int, int]] = []
    selected: list[tuple[int, int]] = []
    selected_indices: list[int] = []
    next_j = 0
    end = 0
    for n in range(stages):
        old_support: set[int] = set()
        for earlier in selected:
            for offset in offsets[: n + 1]:
                old_support.update(interval_support(earlier, offset))
        while True:
            if next_j == len(q_intervals):
                length = rng.randint(1, 23)
                q_intervals.append((end, end + length))
                end += length
            candidate = q_intervals[next_j]
            candidate_j = next_j
            next_j += 1
            if all(not (interval_support(candidate, k) & old_support)
                   for k in offsets[: n + 1]):
                break
        # Independently check every pair required by the stage invariant.
        for r, earlier in enumerate(selected):
            for i, k in enumerate(offsets[: n + 1]):
                for ell, h in enumerate(offsets[: n + 1]):
                    audit.check(
                        not (interval_support(candidate, k)
                             & interval_support(earlier, h)),
                        "fusion_stage_pair", (seed, n, r, i, ell))
        selected.append(candidate)
        selected_indices.append(candidate_j)
    for i, k in enumerate(offsets):
        for ell, h in enumerate(offsets):
            even: set[int] = set()
            odd: set[int] = set()
            early_even: set[int] = set()
            early_odd: set[int] = set()
            cutoff = max(i, ell)
            for n, interval in enumerate(selected):
                if n % 2 == 0:
                    s = interval_support(interval, k)
                    even.update(s)
                    if n < cutoff:
                        early_even.update(s)
                else:
                    s = interval_support(interval, h)
                    odd.update(s)
                    if n < cutoff:
                        early_odd.update(s)
            audit.check(even & odd == early_even & early_odd,
                        "fusion_parity_overlap", (seed, i, ell))
    return {"seed": seed, "stages": stages, "offsets": offsets,
            "selected_interval_indices": selected_indices,
            "selected_intervals": selected}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    audit = Audit()
    selection_path = Path(__file__).resolve().parent / "random_selection.json"
    selection = json.loads(selection_path.read_text(encoding="utf-8"))
    selected = random.Random(int(selection["seed"])).randrange(len(selection["areas"]))
    audit.check(selected == selection["selected_index_0_based"], "random_draw_replay")
    audit.check(selection["areas"][selected] == "Set theory", "random_draw_replay")

    depth = 12
    points: dict[int, int] = {}
    rows: list[dict[str, int]] = []
    running_boundary = 0
    for n in range(depth + 1):
        length = 4**n + 2**(n + 1)
        audit.check(boundary(n) == running_boundary, "boundary_closed_form", n)
        running_boundary += length
        audit.check(boundary(n + 1) == running_boundary, "boundary_recurrence", n)
        for v in range(2**n):
            p = node(n, v)
            audit.check(p not in points, "distinct_node_labels", (n, v))
            points[p] = n
            audit.check(boundary(n) <= p < boundary(n + 1), "node_in_block", (n, v))
            audit.check(p - boundary(n) >= 2**n, "left_margin", (n, v))
            audit.check(boundary(n + 1) - p >= 2**(n + 1), "right_margin", (n, v))
        rows.append({"level": n, "block_start": boundary(n),
                     "block_end_exclusive": boundary(n + 1), "block_length": length,
                     "node_count": 2**n, "first_node": node(n, 0),
                     "last_node": node(n, 2**n - 1), "node_spacing": 2**n})
    ordered = sorted(points)
    for p, q in zip(ordered, ordered[1:]):
        audit.check(q - p >= 2**max(points[p], points[q]),
                    "adjacent_node_separation", (p, q))
    # This test scans all pair distances in the requested shift range,
    # including pairs at different levels and both signs of the shift.
    shift_limit = 512
    collisions = 0
    collision_rows: list[dict[str, int]] = []
    for k in range(-shift_limit, shift_limit + 1):
        if not k:
            continue
        cutoff = abs(k).bit_length()
        hits = 0
        for p, n in points.items():
            q = p - k
            if q in points:
                hits += 1
                collisions += 1
                audit.check(max(n, points[q]) < cutoff,
                            "nonzero_shift_collision_cutoff", (p, q, k))
                audit.check(p < boundary(cutoff),
                            "nonzero_shift_collision_location", (p, k))
        collision_rows.append({"shift": k, "cutoff_level": cutoff,
                               "tree_node_collisions": hits})

    branch_depth = 8
    branches = [prefix_branch(w, branch_depth) for w in range(2**branch_depth)]
    for x, ax in enumerate(branches):
        for y in range(x + 1, len(branches)):
            first_difference = branch_depth - (x ^ y).bit_length()
            audit.check(len(ax & branches[y]) == first_difference + 1,
                        "zero_shift_common_prefix", (x, y))
    branch_shift_limit = 31
    # Membership tests are exact and include x=y as well as x!=y.
    for k in range(-branch_shift_limit, branch_shift_limit + 1):
        if not k:
            continue
        cutoff = abs(k).bit_length()
        shifted_branches = [frozenset(p + k for p in ay if p + k >= 0)
                            for ay in branches]
        for x, ax in enumerate(branches):
            for y, by in enumerate(shifted_branches):
                intersection = ax & by
                audit.check(len(intersection) <= cutoff,
                            "branch_shift_cardinality_bound", (x, y, k))
                audit.check(all(p < boundary(cutoff) for p in intersection),
                            "branch_shift_location_bound", (x, y, k))

    transport_limit = 256
    for p, n in points.items():
        for k in range(-transport_limit, transport_limit + 1):
            if 2**n > abs(k):
                audit.check(boundary(n) <= p + k < boundary(n + 1),
                            "eventual_same_block_transport", (p, n, k))

    fusion_cases = [test_fusion(audit, 20260920 + j, 24) for j in range(8)]
    (out / "fusion_certificates.json").write_text(
        json.dumps(fusion_cases, indent=2) + "\n", encoding="utf-8")
    for filename, data in [("tree_levels.csv", rows), ("shift_collisions.csv", collision_rows)]:
        with (out / filename).open("w", encoding="utf-8", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(data[0]))
            writer.writeheader()
            writer.writerows(data)
    result = {
        "status": "PASS", "python_version": platform.python_version(),
        "implementation": platform.python_implementation(),
        "parameters": {"tree_maximum_level": depth, "tree_node_count": len(points),
                       "tree_shift_limit": shift_limit,
                       "branch_prefix_depth": branch_depth, "branch_count": len(branches),
                       "branch_shift_limit": branch_shift_limit,
                       "transport_shift_limit": transport_limit,
                       "fusion_cases": len(fusion_cases), "fusion_stages": 24},
        "total_checks": sum(audit.counts.values()), "checks_by_category": audit.counts,
        "nonzero_tree_collisions_checked": collisions,
        "limitations": ["No free ultrafilter is constructed or queried.",
                        "No infinite theorem or Baire-category claim is certified by these finite tests.",
                        "This is not a proof-assistant formalization.",
                        "The fusion tests use auxiliary block lengths 3,4,5,...; the written lemma covers all finite-block partitions."]}
    (out / "verification_results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    lines = ["EXACT FINITE VERIFICATION: PASS", "", f"Python {platform.python_version()}",
             f"Total successful checks: {result['total_checks']:,}", ""]
    lines.extend(f"{key}: {value:,}" for key, value in audit.counts.items())
    lines += ["", "LIMITATIONS"] + result["limitations"]
    (out / "verification_report.txt").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print("\n".join(lines))


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError, KeyError) as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
