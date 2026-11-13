#!/usr/bin/env python3
"""Finite checks of two supporting lemmas, NOT verification of the countermodel."""
from itertools import permutations, product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LABELS = (0, 1, 2)
FLIP = (0, 2, 1)
IDENTITY = LABELS


def fixed_points(action):
    return tuple(x for x in LABELS if action[x] == x)


def equivariant_maps(source_action, target_action):
    return [f for f in product(LABELS, repeat=3)
            if all(f[source_action[x]] == target_action[f[x]] for x in LABELS)]


def main():
    transitions = 0
    finite_paths = 0
    for left, middle, right in product((IDENTITY, FLIP), repeat=3):
        for f in equivariant_maps(left, middle):
            for g in equivariant_maps(middle, right):
                transitions += 1
                for start in fixed_points(left):
                    second = f[start]
                    third = g[second]
                    if second not in fixed_points(middle) or third not in fixed_points(right):
                        raise ValueError("An equivariant map failed to preserve fixed fibers")
                    finite_paths += 1
    permutations_checked = 0
    involutions_checked = 0
    for size in range(1, 8):
        for sigma in permutations(range(size)):
            permutations_checked += 1
            if any(sigma[sigma[x]] != x for x in range(size)):
                continue
            involutions_checked += 1
            increasing = all(sigma[x] < sigma[y]
                             for x in range(size) for y in range(x + 1, size))
            if increasing and sigma != tuple(range(size)):
                raise ValueError("A nonidentity involution preserved a finite linear order")
    result = {
        "status": "all finite checks passed",
        "three_fiber_equivariant_map_pairs": transitions,
        "propagated_stabilizer_fixed_paths": finite_paths,
        "permutations_checked_sizes_1_through_7": permutations_checked,
        "involutions_checked": involutions_checked,
        "limitations": [
            "The nonstandard infinite structure is not implemented by this finite script.",
            "Compactness, equivariant global path choice, first-order semantics and bi-interpretability require the written proof.",
            "These finite checks are supporting examples, not Lean/Rocq verification.",
        ],
    }
    (ROOT / "evidence/finite_checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
