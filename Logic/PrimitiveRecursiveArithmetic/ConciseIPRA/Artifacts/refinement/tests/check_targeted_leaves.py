"""Reproduce the targeted 8,008-case dummy-slot computation-leaf audit.

Run from any directory with:
    python3 /path/to/package/tests/check_targeted_leaves.py

This uses the sibling sorted decoder and opener. It is finite implementation
support, not a soundness proof or a check of every rigid-parameter valuation.
It regenerates evidence/twofield_targeted_leaf_audit.json.
"""

import itertools
import json
from pathlib import Path

from check_computation_leaves import compute_leaf, opening, value


def main():
    counters = list(range(12)) + [
        -1, [], [0], [3], [5], [7], [9], [11],
        [0, 3, 3], [0, 5, 3], [0, 0, 5], [0, 0, 7],
        [0, 0], [0, 0, 0, 0],
    ]
    seeds = [
        0, -1, 3, 4, 5, 6, 7, [0], [3], [7],
        [0, 3, 3], [0, 5, 3], [], [3, 3],
    ]
    updates = [
        0, -1, 3, 4, 5, 6, 7, 8, [3], [5], [7], [8], [9],
        [0, 5, 3], [0, 0, 5], [0, 0, 3], [5, 0, [7]],
        [[0], 5, [7]], [0, 3, 3], [0, 5, 5], [3, 0], [0, 3, 0, 0],
    ]
    counts = {
        "proposals": 0, "accepted": 0, "rejected": 0,
        "evaluated_true": 0, "limited": 0,
    }
    counterexamples = []
    for n, seed, update in itertools.product(counters, seeds, updates):
        counts["proposals"] += 1
        try:
            rhs = opening(update, [n, seed, update], 3)
            goal = [[[n], seed, update], rhs]
            if not compute_leaf(goal):
                counts["rejected"] += 1
                continue
        except (TypeError, ValueError, RecursionError):
            counts["rejected"] += 1
            continue
        counts["accepted"] += 1
        try:
            left, right = value(goal[0]), value(goal[1])
            if left != right:
                counterexamples.append({
                    "goal": goal, "left": left, "right": right,
                })
            else:
                counts["evaluated_true"] += 1
        except RuntimeError:
            counts["limited"] += 1
        except IndexError:
            counterexamples.append({
                "goal": goal, "error": "escaping coordinate",
            })
    report = {
        "purpose": "Targeted dummy-slot/outer-state audit of twofield successor leaf",
        "counts": counts,
        "counterexamples": counterexamples,
    }
    target = Path(__file__).resolve().parents[1] / "evidence" / "twofield_targeted_leaf_audit.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    expected = {
        "proposals": 8008, "accepted": 3608, "rejected": 4400,
        "evaluated_true": 3608, "limited": 0,
    }
    if counterexamples or counts != expected:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
