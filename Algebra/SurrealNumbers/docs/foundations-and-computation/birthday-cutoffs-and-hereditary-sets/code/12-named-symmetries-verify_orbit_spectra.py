#!/usr/bin/env python3
"""Finite checks for Named Symmetries and Replacement.

Standard-library only. These checks validate finite action calculations, not
infinite models or Replacement schemes. Run with Python 3.10 or newer.
"""
from __future__ import annotations

import argparse
from collections import deque
from itertools import permutations
import json
from pathlib import Path
import random
from typing import Iterable, Sequence

Permutation = tuple[int, ...]


def validate(generators: Sequence[Permutation]) -> int:
    if not generators:
        raise ValueError("At least one generator is required.")
    n = len(generators[0])
    if n == 0:
        raise ValueError("The action must have a nonempty finite domain.")
    expected = set(range(n))
    if any(len(g) != n or set(g) != expected for g in generators):
        raise ValueError("Every generator must be a permutation of range(n).")
    return n


def inverse(p: Permutation) -> Permutation:
    q = [0] * len(p)
    for i, j in enumerate(p):
        q[j] = i
    return tuple(q)


def compose(p: Permutation, q: Permutation) -> Permutation:
    """p after q, i.e. (p*q)(x)=p(q(x))."""
    if len(p) != len(q):
        raise ValueError("Permutation sizes differ.")
    return tuple(p[q[i]] for i in range(len(p)))


def components(generators: Sequence[Permutation]) -> list[tuple[int, ...]]:
    n = validate(generators)
    steps = list(generators) + [inverse(g) for g in generators]
    unseen = set(range(n))
    result: list[tuple[int, ...]] = []
    while unseen:
        start = min(unseen)
        seen = {start}
        todo = deque([start])
        while todo:
            a = todo.popleft()
            for g in steps:
                b = g[a]
                if b not in seen:
                    seen.add(b)
                    todo.append(b)
        unseen.difference_update(seen)
        result.append(tuple(sorted(seen)))
    return result


def equivariant_maps(
    generators: Sequence[Permutation], source: Sequence[int], target: Sequence[int]
) -> list[dict[int, int]]:
    """All equivariant bijections between two transitive components.

    An equivariant map is determined by the image of one point. Propagate each
    possible image over the Schreier graph; reject inconsistent propagations.
    """
    if not source or len(source) != len(target):
        return []
    source_set, target_set = set(source), set(target)
    steps = list(generators) + [inverse(g) for g in generators]
    maps: list[dict[int, int]] = []
    for image in target:
        mapping = {source[0]: image}
        queue = deque([source[0]])
        consistent = True
        while queue and consistent:
            a = queue.popleft()
            for g in steps:
                a1, b1 = g[a], g[mapping[a]]
                if a1 not in source_set or b1 not in target_set:
                    raise ValueError("Inputs must be invariant components.")
                if a1 in mapping:
                    if mapping[a1] != b1:
                        consistent = False
                        break
                else:
                    mapping[a1] = b1
                    queue.append(a1)
        if consistent and set(mapping) == source_set and set(mapping.values()) == target_set:
            maps.append(mapping)
    return maps


def centralizer_orbits(generators: Sequence[Permutation]) -> list[tuple[int, ...]]:
    """Compute orbits of the full centralizer without enumerating that group."""
    n = validate(generators)
    blocks = components(generators)
    reachable = [{a} for a in range(n)]
    for source in blocks:
        for target in blocks:
            for mapping in equivariant_maps(generators, source, target):
                for a, b in mapping.items():
                    reachable[a].add(b)
    # Every component isomorphism extends by identity, or by its inverse on the
    # target component, to a global commuting permutation.
    for a in range(n):
        for b in reachable[a]:
            if reachable[b] != reachable[a]:
                raise AssertionError("Computed reachability is not an orbit relation.")
    return sorted({tuple(sorted(o)) for o in reachable})


def brute_centralizer_orbits(generators: Sequence[Permutation]) -> list[tuple[int, ...]]:
    n = validate(generators)
    if n > 7:
        raise ValueError("Brute-force cross-check is restricted to n <= 7.")
    reachable = [{a} for a in range(n)]
    for p in permutations(range(n)):
        if all(all(p[g[a]] == g[p[a]] for a in range(n)) for g in generators):
            for a, b in enumerate(p):
                reachable[a].add(b)
    return sorted({tuple(sorted(o)) for o in reachable})


def cyclic_action(n: int, multiplicity: int = 1) -> tuple[Permutation, ...]:
    if n < 1 or multiplicity < 1:
        raise ValueError("Positive size and multiplicity are required.")
    return (tuple(j*n + (i+1) % n for j in range(multiplicity) for i in range(n)),)


def dihedral_copies(n: int, multiplicity: int = 1) -> tuple[Permutation, ...]:
    if n < 1 or multiplicity < 1:
        raise ValueError("Positive size and multiplicity are required.")
    sigma = tuple(j*n + (-i) % n for j in range(multiplicity) for i in range(n))
    tau = tuple(j*n + (1-i) % n for j in range(multiplicity) for i in range(n))
    return sigma, tau


def disjoint_union(actions: Iterable[Sequence[Permutation]]) -> tuple[Permutation, ...]:
    actions = list(actions)
    if not actions:
        raise ValueError("At least one action is required.")
    m = len(actions[0])
    result: list[list[int]] = [[] for _ in range(m)]
    offset = 0
    for action in actions:
        n = validate(action)
        if len(action) != m:
            raise ValueError("Generator signatures differ.")
        for j, g in enumerate(action):
            result[j].extend(offset + a for a in g)
        offset += n
    return tuple(tuple(g) for g in result)


def run_tests() -> dict[str, object]:
    checks = 0
    examples: list[dict[str, object]] = []
    # Regular cyclic actions: centralizer orbits have n*m points.
    for n in range(1, 15):
        for m in range(1, 5):
            action = cyclic_action(n, m)
            assert centralizer_orbits(action) == [tuple(range(n*m))]
            checks += 1
    # Odd dihedral components are rigid; repeated components give m-point orbits.
    for n in (3, 5, 7, 9, 11, 13, 15, 17, 19):
        for d in range(1, 10):
            action = dihedral_copies(n, d)
            identity = tuple(range(n*d))
            assert all(compose(g, g) == identity for g in action)
            orbits = centralizer_orbits(action)
            expected = sorted(tuple(j*n+i for j in range(d)) for i in range(n))
            assert orbits == expected
            r = compose(action[1], action[0])
            assert all(r[j*n+i] == j*n + (i+1) % n for j in range(d) for i in range(n))
            sigma_fixed = [a for a in range(n*d) if action[0][a] == a]
            assert sigma_fixed == [j*n for j in range(d)]
            checks += 1
            if n in (3, 9, 19) and d in (1, 2, 5, 9):
                examples.append({"cycle_length": n, "multiplicity": d,
                                 "centralizer_orbit_size": len(orbits[0]),
                                 "sigma_fixed_points": len(sigma_fixed)})
    # Even lengths are deliberate negative controls: local automorphism size 2.
    for n in (4, 6, 8, 10, 12):
        for m in range(1, 5):
            orbits = centralizer_orbits(dihedral_copies(n, m))
            assert all(len(o) == 2*m for o in orbits)
            assert len(orbits) == n//2
            checks += 1
    # Distinct component lengths cannot be interchanged. This is a finite
    # truncation of the strict-hierarchy example, not itself a failing model.
    for d in range(1, 8):
        action = disjoint_union(dihedral_copies(n, d) for n in (3, 5, 7, 9))
        orbits = centralizer_orbits(action)
        assert len(orbits) == 24 and all(len(o) == d for o in orbits)
        checks += 1
    # Independent exhaustive cross-check on deterministic random actions.
    rng = random.Random(20261003)
    cross_checks = 0
    for n in range(1, 8):
        for _ in range(5):
            gs: list[Permutation] = []
            for _ in range(2):
                values = list(range(n))
                rng.shuffle(values)
                gs.append(tuple(values))
            assert centralizer_orbits(gs) == brute_centralizer_orbits(gs)
            checks += 1
            cross_checks += 1
    for bad in ((), ((0, 0),), ((),), ((0, 1), (0,))):
        try:
            validate(bad)
        except ValueError:
            checks += 1
        else:
            raise AssertionError("Invalid permutation input was accepted.")
    return {"status": "PASS", "checks": checks,
            "independent_brute_force_cross_checks": cross_checks,
            "random_seed": 20261003,
            "scope": "Finite centralizer and witness calculations only; no verification of infinite Replacement schemes.",
            "selected_examples": examples}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("verification_results.json"))
    args = parser.parse_args()
    results = run_tests()
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"{results['status']}: {results['checks']} checks; "
          f"{results['independent_brute_force_cross_checks']} independent brute-force comparisons.")
    print(f"Results written to {args.output}")


if __name__ == "__main__":
    main()
