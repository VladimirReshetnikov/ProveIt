#!/usr/bin/env python3
"""Independent, reproducible audit of the order-ideal transform.

Run with Python 3.9 or later.  The default run reconstructs the 1,800
random-poset audit discussed in the research notes.  It checks the fast
zeta transform against direct summation, its inverse against the original
integer table, the maximal-element formula for the inverse, and the
Boolean coefficient-filter identity.  It also includes the empty poset
and a regression showing that inverse-transform order matters.

This checks finite combinatorial identities, not topological authenticity
or determinant/witness-extraction code.  It imports no project modules.
"""

import argparse
import hashlib
import json
from pathlib import Path
from random import Random


def enumerate_ideals(ancestors):
    """Exhaustive independent oracle; labels form a linear extension."""
    size = len(ancestors)
    return [
        mask
        for mask in range(1 << size)
        if all(
            not (mask & (1 << vertex))
            or (ancestors[vertex] & mask) == ancestors[vertex]
            for vertex in range(size)
        )
    ]


def transform(table, ideals, size, inverse=False):
    """Fast ideal-state zeta, or inverse in REVERSE extension order."""
    values = table.copy()
    ideal_set = set(ideals)
    order = reversed(range(size)) if inverse else range(size)
    sign = -1 if inverse else 1
    for vertex in order:
        bit = 1 << vertex
        for mask in ideals:
            if (mask & bit) and (mask ^ bit) in ideal_set:
                values[mask] += sign * values[mask ^ bit]
    return values


def direct_zeta(table, ideals):
    return {
        mask: sum(value for submask, value in table.items() if submask & mask == submask)
        for mask in ideals
    }


def explicit_mobius(table, ideals, size):
    """Use c(A)=sum_{S subset max(A)}(-1)^|S| g(A minus S)."""
    ideal_set = set(ideals)
    result = {}
    for mask in ideals:
        maximal = sum(
            1 << vertex
            for vertex in range(size)
            if mask & (1 << vertex) and mask ^ (1 << vertex) in ideal_set
        )
        value = 0
        submask = maximal
        while True:
            parity = bin(submask).count("1") & 1
            value += (-1 if parity else 1) * table[mask ^ submask]
            if submask == 0:
                break
            submask = (submask - 1) & maximal
        result[mask] = value
    return result


def random_poset(size, rng):
    """Take random forward edges, then compute exact transitive ancestors."""
    ancestors = [0] * size
    for upper in range(size):
        for lower in range(upper):
            if rng.randrange(4) == 0:
                ancestors[upper] |= (1 << lower) | ancestors[lower]
    return ancestors


def run(seed, trials_per_size, max_size):
    rng = Random(seed)
    by_size = []
    random_posets = 0
    ideal_states = 0

    # The zero-dimensional determinant-filter case has one state.
    empty_ideals = enumerate_ideals([])
    assert empty_ideals == [0]
    assert transform({0: 1}, empty_ideals, 0, inverse=True) == {0: 1}

    # Chain a < b: inverse order is essential.
    chain_ideals = enumerate_ideals([0, 1])
    chain_g = {0: 1, 1: 3, 3: 7}
    chain_expected = {0: 1, 1: 2, 3: 4}
    assert transform(chain_g, chain_ideals, 2, inverse=True) == chain_expected
    wrong = chain_g.copy()
    for vertex in range(2):
        for mask in chain_ideals:
            if mask & (1 << vertex) and mask ^ (1 << vertex) in wrong:
                wrong[mask] -= wrong[mask ^ (1 << vertex)]
    assert wrong != chain_expected

    for size in range(1, max_size + 1):
        size_states = 0
        largest_ideal_count = 0
        for trial in range(trials_per_size):
            ancestors = random_poset(size, rng)
            ideals = enumerate_ideals(ancestors)
            original = {mask: rng.randrange(-20, 21) for mask in ideals}

            zeta = transform(original, ideals, size)
            assert zeta == direct_zeta(original, ideals), ("zeta", size, trial)
            assert transform(zeta, ideals, size, inverse=True) == original, (
                "inverse", size, trial
            )
            assert explicit_mobius(zeta, ideals, size) == original, (
                "maximal-element formula", size, trial
            )

            # For arbitrary Boolean g(K)=f(P\K), the coefficient of a
            # basis whose missed set is K must be exactly g(K).
            # Reuse the sampled table so no extra RNG calls change the
            # originally reported random-poset sequence.
            boolean_g = {mask: value & 1 for mask, value in original.items()}
            coefficients = transform(boolean_g, ideals, size, inverse=True)
            assert direct_zeta(coefficients, ideals) == boolean_g, (
                "Boolean filter", size, trial
            )
            assert coefficients == explicit_mobius(boolean_g, ideals, size), (
                "Boolean coefficient formula", size, trial
            )

            count = len(ideals)
            size_states += count
            largest_ideal_count = max(largest_ideal_count, count)
            ideal_states += count
            random_posets += 1
        by_size.append({
            "size": size,
            "random_posets": trials_per_size,
            "ideal_states": size_states,
            "largest_ideal_count": largest_ideal_count,
        })

    return {
        "schema_version": 1,
        "audit": "independent_order_ideal_transform",
        "scope": "Finite ideal-lattice transforms and Boolean filter identity; no topology or determinant-code claims.",
        "seed": seed,
        "trials_per_size": trials_per_size,
        "size_range": [1, max_size],
        "random_posets": random_posets,
        "ideal_states": ideal_states,
        "mismatches": 0,
        "checks": {
            "fast_zeta_equals_direct_subset_sum": True,
            "inverse_recovers_integer_table": True,
            "inverse_equals_maximal_element_formula": True,
            "filtered_basis_multipliers_equal_zero_or_one": True,
            "empty_poset": True,
            "wrong_inverse_order_is_detected": True,
        },
        "by_size": by_size,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=7421901)
    parser.add_argument("--trials-per-size", type=int, default=200)
    parser.add_argument("--max-size", type=int, default=9)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_suffix(".json"))
    args = parser.parse_args()
    if args.trials_per_size < 1 or args.max_size < 1:
        parser.error("trial count and maximum size must be positive")
    result = run(args.seed, args.trials_per_size, args.max_size)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
