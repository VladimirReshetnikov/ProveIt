#!/usr/bin/env python3
"""Finite diagnostics for the hereditary one-support obstruction.

These finite structures are NOT models of the full EPSC schema.  The script
checks the finite symmetry lemmas used in the report, and explicitly exhibits
an EPSC instance that the truncated structure fails.  No third-party modules.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def apply_mask(mask, permutation):
    result = 0
    while mask:
        bit = mask & -mask
        result |= 1 << permutation[bit.bit_length() - 1]
        mask ^= bit
    return result


def subsets(count):
    return range(1 << count)


def bit_indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def support_table(index_count, phases):
    permutations = list(itertools.permutations(range(index_count)))
    actions = [tuple(phases * p[i] + s
                     for i in range(index_count) for s in range(phases))
               for p in permutations]
    stabilizers = {
        support: [a for p, a in zip(permutations, actions)
                  if all(p[i] == i for i in bit_indices(support))]
        for support in subsets(index_count)
    }
    support_order = sorted(subsets(index_count), key=lambda s: (s.bit_count(), s))
    minima = {}
    for mask in subsets(index_count * phases):
        minima[mask] = next(s for s in support_order
                            if all(apply_mask(mask, a) == mask
                                   for a in stabilizers[s]))
    return permutations, actions, minima


def base_structure(index_count=4, phases=2):
    permutations, actions, minima = support_table(index_count, phases)
    primitive_count = index_count * phases
    extensions = [1 << (phases * i + (s + 1) % phases)
                  for i in range(index_count) for s in range(phases)]
    supported_masks = [m for m in subsets(primitive_count)
                       if minima[m].bit_count() <= 1]
    ordinary_masks = [m for m in supported_masks if m.bit_count() != 1]
    extensions.extend(ordinary_masks)
    require(len(set(extensions)) == len(extensions), "Extensionality failed")
    require(all(not (members >> i) & 1 for i, members in enumerate(extensions)),
            "Irreflexivity failed")
    require(all(m < (1 << primitive_count) for m in extensions),
            "Truncated structure is not membership-transitive")
    empty = extensions.index(0)
    # The next-rank singleton of the empty node is absent from this truncation.
    require((1 << empty) not in extensions, "Expected rank-cutoff control absent")
    pair = (1 << 0) | (1 << phases)
    require(minima[pair].bit_count() == 2, "Cross-index pair needs two supports")
    require(pair not in extensions, "Forbidden exact pair unexpectedly present")
    singleton_normalization = [
        {"member": phases * i + s,
         "representative": phases * i + (s - 1) % phases}
        for i in range(index_count) for s in range(phases)
    ]
    for row in singleton_normalization:
        require(extensions[row["representative"]] == 1 << row["member"],
                "Singleton normalization mismatch")
    return {
        "indices": index_count,
        "phases": phases,
        "group_size": len(permutations),
        "primitive_objects": primitive_count,
        "all_base_subsets": 1 << primitive_count,
        "support_size_histogram": dict(sorted(Counter(
            s.bit_count() for s in minima.values()).items())),
        "base_subsets_with_support_at_most_one": len(supported_masks),
        "ordinary_nodes_after_singleton_normalization": len(ordinary_masks),
        "truncated_structure_objects": len(extensions),
        "extensional": True,
        "irreflexive": True,
        "cross_index_pair_minimum_support": minima[pair].bit_count(),
        "cross_index_pair_absent": True,
        "singleton_normalization": singleton_normalization,
        "NOT_a_full_EPSC_model": {
            "empty_node": empty,
            "missing_singleton_of_empty_extension_mask": 1 << empty,
            "failed_matrix": "rho(x,y) := Empty(y)",
            "reason": "Locally bounded constant output {empty} has no exact hull in this rank cutoff."
        },
    }


def pair_orbits(actions, size):
    unseen = set(itertools.product(range(size), repeat=2))
    orbits = []
    while unseen:
        x, y = min(unseen)
        orbit = {(p[x], p[y]) for p in actions}
        require(orbit <= unseen, "Pair orbit overlap")
        unseen -= orbit
        row_masks = [0] * size
        for a, b in orbit:
            row_masks[a] |= 1 << b
        orbits.append(row_masks)
    return orbits


def exhaustive_closures(fix_index):
    # Carrier: four phase-zero primitive objects, the empty object e, and
    # the invariant object containing all four phase-zero primitives.
    # The ambient bounding object contains BOTH phases.  Hull representatives
    # may lie above this finite carrier; no finite-model claim is made.
    indices, size, empty = 4, 6, 4
    raw = list(itertools.permutations(range(indices)))
    raw = [p for p in raw if fix_index is None or p[fix_index] == fix_index]
    actions = [p + (4, 5) for p in raw]
    orbits = pair_orbits(actions, size)
    invariant_masks = {m for m in subsets(size)
                       if all(apply_mask(m, p) == m for p in actions)}
    count = 1 << len(orbits)
    adjacency = [0] * size
    last_gray = 0
    histogram = Counter()
    closure_rounds = Counter()
    prefixed_checks = 0
    for k in range(count):
        gray = k ^ (k >> 1)
        if k:
            changed = (gray ^ last_gray).bit_length() - 1
            for row, mask in enumerate(orbits[changed]):
                adjacency[row] ^= mask
        last_gray = gray
        # Images of every carrier subset; useful for independently checking
        # leastness against ALL prefixed carrier subsets.
        images = [0] * (1 << size)
        for mask in range(1, 1 << size):
            bit = mask & -mask
            images[mask] = images[mask ^ bit] | adjacency[bit.bit_length() - 1]
        root = 1 << empty
        current, rounds = 0, 0
        while True:
            nxt = images[current | root]
            require(current & ~nxt == 0, "Iteration lost monotonicity")
            if nxt == current:
                break
            current = nxt
            rounds += 1
            require(rounds <= size, "Finite closure exceeded carrier height")
        require(current in invariant_masks, "Equivariant hull lost its support")
        require(images[current | root] == current, "Hull is not an exact fixed point")
        for candidate in subsets(size):
            image = images[candidate | root]
            if image & ~candidate == 0:
                require(current & ~candidate == 0, "Hull is not globally least")
                prefixed_checks += 1
        histogram[current.bit_count()] += 1
        closure_rounds[rounds] += 1
    return {
        "parameter_support": [] if fix_index is None else [fix_index],
        "stabilizer_order": len(actions),
        "carrier_size": size,
        "ordered_pair_orbits": len(orbits),
        "equivariant_relations_exhausted": count,
        "support_preserving_exact_least_hulls": count,
        "prefixed_subset_comparisons": prefixed_checks,
        "hull_cardinality_histogram": dict(sorted(histogram.items())),
        "strict_iteration_rounds_histogram": dict(sorted(closure_rounds.items())),
        "scope": "Finite group-action lemma only; not an EPSC model or a definability census."
    }


def negative_controls():
    # Three indices do NOT witness the support obstruction: fixing the omitted
    # third index already fixes the unordered pair of the other two.
    _, _, small = support_table(3, 2)
    pair = (1 << 0) | (1 << 2)
    require(small[pair].bit_count() == 1, "Three-index caution control changed")
    # The two-parameter constant relation demands the forbidden exact pair.
    _, _, large = support_table(4, 2)
    require(large[pair].bit_count() == 2, "Two-parameter obstruction missing")
    # Full orbit saturation supplies a closed hull, but adds unwanted outputs.
    all_phase_zero = sum(1 << (2 * i) for i in range(4))
    require(pair != all_phase_zero and (pair & ~all_phase_zero) == 0,
            "Orbit padding did not introduce extra members")
    require(large[all_phase_zero].bit_count() == 0,
            "Full orbit union must have empty support")
    return {
        "three_index_pair_support": small[pair].bit_count(),
        "four_index_pair_support": large[pair].bit_count(),
        "two_parameter_constant_hull_extension_mask": pair,
        "support_free_orbit_hull_extension_mask": all_phase_zero,
        "support_clause_fails_after_orbit_padding": True,
        "reason": "The added primitive objects are not in the constant relation's range."
    }


def run():
    return {
        "status": "passed",
        "claim_type": "Exhaustive finite diagnostics for an ordinary mathematical proof",
        "base": base_structure(),
        "closure_families": [exhaustive_closures(None), exhaustive_closures(0)],
        "negative_controls": negative_controls(),
        "formal_kernel_checked": False,
        "finite_model_of_full_schema_claimed": False,
        "consistency_strength_separation_claimed": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"],
                      "relations": sum(r["equivariant_relations_exhausted"]
                                       for r in result["closure_families"]),
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
