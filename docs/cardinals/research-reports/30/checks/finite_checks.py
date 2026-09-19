#!/usr/bin/env python3
"""Finite audits for Prikry_Symmetry.tex (not a proof of the forcing theorems).

Requires Python 3.9 or newer and only its standard library. Output is a
reproducible JSON record beside this script. Failures raise AssertionError.
"""
from __future__ import annotations

import itertools
import json
from collections import Counter
from pathlib import Path
from typing import Dict, List, Tuple

Permutation = Tuple[int, ...]


def inverse(p: Permutation) -> Permutation:
    inv = [0] * len(p)
    for i, value in enumerate(p):
        inv[value] = i
    return tuple(inv)


def apply_power(p: Permutation, i: int, n: int) -> int:
    if n < 0:
        return apply_power(inverse(p), i, -n)
    for _ in range(n):
        i = p[i]
    return i


def binary_table_orbits(n: int) -> Dict[str, object]:
    """Exhaust all tournaments under cyclic relabelling of their vertices."""
    pairs = list(itertools.combinations(range(n), 2))
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    tau = tuple((i + 1) % n for i in range(n))
    inv = inverse(tau)
    # Destination bit i receives a source bit, possibly reversed in orientation.
    transforms = []
    for x, y in pairs:
        old_x, old_y = inv[x], inv[y]
        old_pair = tuple(sorted((old_x, old_y)))
        src = pair_index[old_pair]
        transforms.append((src, old_x > old_y))

    def act(table: int) -> int:
        result = 0
        for dest, (src, flip) in enumerate(transforms):
            bit = ((table >> src) & 1) ^ int(flip)
            result |= bit << dest
        return result

    count = 1 << len(pairs)
    unseen = set(range(count))
    orbit_sizes: Counter[int] = Counter()
    while unseen:
        start = min(unseen)
        orbit = {start}
        current = act(start)
        while current != start:
            assert current not in orbit, "Action did not return to its starting point"
            orbit.add(current)
            current = act(current)
        unseen.difference_update(orbit)
        orbit_sizes[len(orbit)] += 1
    expected_minimum = {2: 2, 3: 1, 4: 4, 6: 2}[n]
    assert min(orbit_sizes) == expected_minimum
    assert sum(size * number for size, number in orbit_sizes.items()) == count
    return {
        "N": n,
        "number_of_tables": count,
        "orbit_size_histogram": dict(sorted(orbit_sizes.items())),
        "minimum_orbit_size": min(orbit_sizes),
        "expected_minimum": expected_minimum,
    }


def check_block_insertion() -> Dict[str, int]:
    """Pairs (base, offset) exactly encode the ordinal blocks used in the proof."""
    cases = 0
    identities = 0
    c = tuple(100 + 10 * i for i in range(20))
    for m in range(1, 6):
        for pi in itertools.permutations(range(m)):
            inv = inverse(pi)
            for ell in range(6):
                alpha = c[ell] - 1
                d = c[:ell] + (alpha,) + c[ell:]
                for i in range(m):
                    for n in range(ell, len(c)):
                        new_block = (d[n + 1], apply_power(pi, i, -(n + 1)))
                        old_block = (c[n], apply_power(pi, inv[i], -n))
                        assert new_block == old_block
                        identities += 1
                cases += 1
    return {"permutation_insertion_cases": cases, "pointwise_identities": identities}


def index(a: frozenset[int], b: frozenset[int]) -> int:
    return len(b - a) - len(a - b)


def check_phase_cocycle() -> Dict[str, int]:
    # A common infinite tail cancels; finite initial pieces suffice for this identity.
    pieces = [frozenset(i for i in range(5) if (mask >> i) & 1)
              for mask in range(1 << 5)]
    triples = 0
    for a, b, c in itertools.product(pieces, repeat=3):
        assert index(a, c) == index(a, b) + index(b, c)
        triples += 1
    translations = 0
    for a in pieces:
        d = a | {10}
        assert index(a, d) == 1
        for b in pieces:
            assert index(d, b) == index(a, b) - 1
            for modulus in range(2, 9):
                assert index(d, b) % modulus == (index(a, b) - 1) % modulus
                translations += 1
    return {"cocycle_triples": triples, "phase_translation_checks": translations}


def check_shift_partition() -> Dict[str, int]:
    checks = 0
    for shift in range(-20, 21):
        if shift == 0:
            continue
        k = abs(shift)
        for n in range(-500, 501):
            assert ((n // k) % 2) != (((n + shift) // k) % 2)
            checks += 1
    return {"alternating_block_checks": checks}


def main() -> None:
    results = {
        "status": "passed",
        "scope": "Finite algebra and sign conventions only; not formal verification of set theory.",
        "binary_table_orbits": [binary_table_orbits(n) for n in (2, 3, 4, 6)],
        "block_insertion": check_block_insertion(),
        "phase_cocycle": check_phase_cocycle(),
        "shift_partition": check_shift_partition(),
    }
    path = Path(__file__).resolve().with_name("results.json")
    text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    path.write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
