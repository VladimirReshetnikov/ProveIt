#!/usr/bin/env python3
"""Finite checks accompanying Finite Symmetry at Measurable Strength.

Uses only the Python standard library. These tests do NOT verify any forcing,
inner-model, large-cardinal, ultrafilter-existence, or consistency claim.
Run: python3 checks/finite_checks.py
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product
from math import comb, gcd, lcm
from typing import Iterable


Permutation = tuple[int, ...]


def bits(indices: Iterable[int]) -> int:
    return sum(1 << i for i in indices)


def compose(p: Permutation, q: Permutation) -> Permutation:
    """p after q, for the convention used for the left permutation action."""
    return tuple(p[q[i]] for i in range(len(p)))


def orbit_under(p: Permutation) -> set[Permutation]:
    identity = tuple(range(len(p)))
    found = {identity}
    current = p
    while current != identity:
        assert current not in found, "Malformed permutation power cycle"
        found.add(current)
        current = compose(p, current)
    return found


def selector_orbits(N: int, n: int, r: int) -> tuple[int, Counter[int]]:
    """Exhaust all tables [N]^n -> [N]^r choosing a subset of each input."""
    inputs = tuple(bits(c) for c in combinations(range(N), n))
    input_index = {mask: i for i, mask in enumerate(inputs)}
    options = [tuple(bits(c) for c in combinations(
        tuple(i for i in range(N) if mask & (1 << i)), r)) for mask in inputs]
    full_mask = (1 << N) - 1
    rotate = tuple(((mask << 1) & full_mask) | (mask >> (N - 1))
                   for mask in range(1 << N))
    inverse = lambda mask: (mask >> 1) | ((mask & 1) << (N - 1))
    predecessor = tuple(input_index[inverse(mask)] for mask in inputs)

    def act(table: tuple[int, ...]) -> tuple[int, ...]:
        # (tau . table)(B) = tau(table(tau^{-1}(B))).
        return tuple(rotate[table[j]] for j in predecessor)

    visited: set[tuple[int, ...]] = set()
    orbit_sizes: Counter[int] = Counter()
    for table in product(*options):
        if table in visited:
            continue
        current = table
        size = 0
        while current not in visited:
            visited.add(current)
            size += 1
            current = act(current)
        assert current == table
        assert N % size == 0
        orbit_sizes[size] += 1
    expected = comb(n, r) ** comb(N, n)
    assert len(visited) == expected
    assert sum(size * count for size, count in orbit_sizes.items()) == expected
    return expected, orbit_sizes


def check_selectors() -> tuple[int, int, int]:
    print("SELECTOR TABLES (all cases N <= 6 with at most 100,000 tables)")
    total_tables = cases = amplified_cases = 0
    for N in range(2, 7):
        for n in range(2, N + 1):
            for r in range(1, n):
                if comb(n, r) ** comb(N, n) > 100_000:
                    continue
                total, orbits = selector_orbits(N, n, r)
                cases += 1
                total_tables += total
                minimum = min(orbits)
                tested_M = []
                for M in range(1, 7):
                    L = lcm(*range(1, M + 1))
                    if N == n * L:
                        assert minimum > M, (N, n, r, M, minimum)
                        amplified_cases += 1
                        tested_M.append(M)
                if N == n:
                    # An invariant r-subset for tau^ell is a union of
                    # cycles, so n/gcd(n,r) divides each table-orbit length.
                    assert all(length % (n // gcd(n, r)) == 0 for length in orbits)
                print(f"  N={N}, n={n}, r={r}: {total} tables; "
                      f"orbits(size:count)={dict(sorted(orbits.items()))}; "
                      f"amplification M={tested_M}")
    print(f"  PASS: {cases} cases; {total_tables} tables; "
          f"{amplified_cases} cycle-amplification instances.\n")
    return cases, total_tables, amplified_cases


def check_incidence_words() -> tuple[int, int]:
    """Periodic words: tail equivalence is equivalence under cyclic rotation."""
    print("PERIODIC INCIDENCE WORDS")
    candidates = distinct_column_words = 0
    for m, maximum_period in ((1, 5), (2, 5), (3, 5), (4, 3)):
        perms = tuple(permutations(range(m)))
        mask_actions = {
            p: tuple(bits(p[i] for i in range(m) if mask & (1 << i))
                     for mask in range(1 << m))
            for p in perms
        }
        power_groups = {p: orbit_under(p) for p in perms}
        checked = 0
        group_orders: Counter[int] = Counter()
        for period in range(1, maximum_period + 1):
            for word in product(range(1, 1 << m), repeat=period):
                candidates += 1
                columns = tuple(tuple(bool(mask & (1 << i)) for mask in word)
                                for i in range(m))
                if len(set(columns)) != m:
                    continue
                rotations = {word[k:] + word[:k] for k in range(period)}
                stabilizer = {
                    p for p in perms
                    if tuple(mask_actions[p][mask] for mask in word) in rotations
                }
                assert stabilizer, "The identity must stabilize the tail class"
                assert any(power_groups[p] == stabilizer for p in stabilizer), (
                    m, word, stabilizer
                )
                checked += 1
                group_orders[len(stabilizer)] += 1
        distinct_column_words += checked
        print(f"  m={m}, periods 1..{maximum_period}: {checked} words with "
              f"distinct columns; stabilizer orders={dict(sorted(group_orders.items()))}")
    print(f"  PASS: {candidates} candidate words; "
          f"{distinct_column_words} cyclic stabilizers checked.\n")
    return candidates, distinct_column_words


def check_five_labels() -> None:
    print("THE FIVE-LABEL S_3 ACTION")
    common = set(range(5))
    for p in permutations(range(3)):
        odd = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)) % 2
        action = tuple(p) + ((4, 3) if odd else (3, 4))
        fixed = {i for i in range(5) if action[i] == i}
        assert fixed
        common.intersection_update(fixed)
        print(f"  {p}: fixed labels {sorted(fixed)}")
    assert not common
    print("  PASS: every permutation fixes a label; no common fixed label.\n")


def check_index() -> tuple[int, int]:
    print("FINITE-CHANGE INDEX AND DELETION PHASES")
    # Attach the same infinite tail above these finite prefixes. Then all
    # sets represent the same finite-change class. Prefixes are encoded by masks.
    prefixes = tuple(range(1 << 5))
    index = lambda a, b: (a & ~b).bit_count() - (b & ~a).bit_count()
    triples = 0
    for a, b, c in product(prefixes, repeat=3):
        assert index(a, c) == index(a, b) + index(b, c)
        triples += 1
    deletions = 0
    for a in prefixes:
        for beta in range(5):
            if not a & (1 << beta):
                continue
            aminus = a & ~(1 << beta)
            for b in prefixes:
                assert index(aminus, b) == index(a, b) - 1
                for h in range(1, 9):
                    assert index(aminus, b) % h == (index(a, b) - 1) % h
                deletions += 1
    for h in range(2, 13):
        for mask in range(1, (1 << h) - 1):
            shift = (mask >> 1) | ((mask & 1) << (h - 1))
            assert mask != shift, "A nonempty proper set is not rotation invariant"
    print(f"  PASS: {triples} cocycle triples; {deletions} deletions "
          "(each checked modulo 1..8).")
    print("  PASS: nonempty proper residue sets for moduli 2..12 are not shift invariant.\n")
    return triples, deletions


def main() -> None:
    print("Finite Symmetry at Measurable Strength: reproducible finite checks")
    print("No external dependencies. Exhaustive checks within the stated bounds.\n")
    check_selectors()
    check_incidence_words()
    check_five_labels()
    check_index()
    print("ALL FINITE CHECKS PASSED.")
    print("These are finite combinatorial checks only, not a formal verification")
    print("of forcing, genericity, HOD, ultrafilter existence, or consistency.")


if __name__ == "__main__":
    main()
