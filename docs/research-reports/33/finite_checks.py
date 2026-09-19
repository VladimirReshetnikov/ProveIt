#!/usr/bin/env python3
"""Exact finite checks for Prikry_Finite_Symmetry.tex.

These checks concern finite permutation algebra only. They do not verify
forcing, ordinal definability, measurable cardinals, or the existence of
ultrafilters. Requires Python 3.10+; no third-party packages.
"""
from __future__ import annotations

from collections import Counter
from itertools import combinations, permutations, product
from math import lcm
from typing import Iterable

Permutation = tuple[int, ...]


def compose(p: Permutation, q: Permutation) -> Permutation:
    """Return p after q, in the convention (p q)(i) = p(q(i))."""
    if len(p) != len(q):
        raise ValueError("Permutation sizes must agree.")
    return tuple(p[q[i]] for i in range(len(p)))


def cyclic_subgroup(p: Permutation) -> frozenset[Permutation]:
    identity = tuple(range(len(p)))
    out = {identity}
    q = p
    while q not in out:
        out.add(q)
        q = compose(p, q)
    assert q == identity
    return frozenset(out)


def cycles(p: Permutation) -> list[list[int]]:
    if sorted(p) != list(range(len(p))):
        raise ValueError("Not a permutation.")
    unseen = set(range(len(p)))
    out: list[list[int]] = []
    while unseen:
        i = min(unseen)
        cycle: list[int] = []
        while i in unseen:
            cycle.append(i)
            unseen.remove(i)
            i = p[i]
        assert i == cycle[0]
        out.append(cycle)
    return out


def check_amplification() -> int:
    checked = 0
    for n in range(1, 7):
        for p in permutations(range(n)):
            decomposition = cycles(p)
            for bound in range(1, 6):
                H = lcm(*range(1, bound + 1))
                v: dict[int, tuple[int, int]] = {}
                lengths = [H * len(cycle) for cycle in decomposition]
                for j, cycle in enumerate(decomposition):
                    for s, i in enumerate(cycle):
                        v[i] = (j, H * s)
                assert len(set(v.values())) == n
                for i in range(n):
                    j, t = v[i]
                    tau_H_v_i = (j, (t + H) % lengths[j])
                    assert tau_H_v_i == v[p[i]]
                # Every permutation of <= bound points has cycle lengths
                # dividing H; test all such permutations up to this bound.
                for size in range(1, bound + 1):
                    assert H % size == 0
                checked += 1
    return checked


def bitmask(values: Iterable[int]) -> int:
    result = 0
    for value in values:
        result |= 1 << value
    return result


def selector_orbits(N: int, n: int, r: int) -> tuple[int, Counter[int]]:
    """Exhaustively compute cyclic conjugation orbits of selector tables."""
    if not 0 < r < n <= N:
        raise ValueError("Need 0 < r < n <= N.")
    domain = list(combinations(range(N), n))
    index = {B: i for i, B in enumerate(domain)}
    options = [tuple(bitmask(C) for C in combinations(B, r)) for B in domain]
    inverse_input = [index[tuple(sorted((i - 1) % N for i in B))] for B in domain]
    fullmask = (1 << N) - 1

    def rotate(table: tuple[int, ...]) -> tuple[int, ...]:
        output: list[int] = []
        for old_index in inverse_input:
            value = table[old_index]
            output.append(((value << 1) & fullmask) | (value >> (N - 1)))
        return tuple(output)

    visited: set[tuple[int, ...]] = set()
    distribution: Counter[int] = Counter()
    total = 0
    for table in product(*options):
        total += 1
        if table in visited:
            continue
        orbit: set[tuple[int, ...]] = set()
        current = table
        while current not in orbit:
            assert current not in visited
            orbit.add(current)
            current = rotate(current)
        assert current == table
        assert N % len(orbit) == 0
        visited.update(orbit)
        distribution[len(orbit)] += 1
    assert len(visited) == total == sum(k * v for k, v in distribution.items())
    return total, distribution


def five_label_action(p: Permutation, label: int) -> int:
    if len(p) != 3 or not 0 <= label < 5:
        raise ValueError("Expected an S3 permutation and a label in range(5).")
    if label < 3:
        return p[label]
    parity = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)) % 2
    return 3 + ((label - 3 + parity) % 2)


def check_five_labels() -> list[tuple[Permutation, list[int]]]:
    group = list(permutations(range(3)))
    rows = [(p, [i for i in range(5) if five_label_action(p, i) == i]) for p in group]
    assert all(fixed for _, fixed in rows)
    assert not set.intersection(*(set(fixed) for _, fixed in rows))
    for p in group:
        for q in group:
            for i in range(5):
                assert five_label_action(compose(p, q), i) == five_label_action(
                    p, five_label_action(q, i)
                )
    return rows


def permute_mask(mask: int, p: Permutation) -> int:
    return bitmask(p[i] for i in range(len(p)) if mask & (1 << i))


def check_periodic_word_stabilizers() -> Counter[int]:
    """All periods 1..4 over the seven nonempty subsets of three labels."""
    group = tuple(permutations(range(3)))
    histogram: Counter[int] = Counter()
    for period in range(1, 5):
        for word in product(range(1, 8), repeat=period):
            # Each label occurs, and every pair is separated in one period.
            if any(not any(mask & (1 << i) for mask in word) for i in range(3)):
                continue
            if any(
                not any(bool(mask & (1 << i)) != bool(mask & (1 << j)) for mask in word)
                for i, j in combinations(range(3), 2)
            ):
                continue
            stabilizer = frozenset(
                p for p in group
                if any(
                    all(word[(k + d) % period] == permute_mask(word[k], p)
                        for k in range(period))
                    for d in range(period)
                )
            )
            assert stabilizer
            assert any(cyclic_subgroup(p) == stabilizer for p in stabilizer)
            histogram[len(stabilizer)] += 1
    # Without label separation the lemma would be false.
    full_group = frozenset(group)
    assert not any(cyclic_subgroup(p) == full_group for p in full_group)
    assert all(permute_mask(7, p) == 7 for p in group)
    return histogram


def check_phase_and_residues() -> None:
    universe = range(5)
    subsets = [frozenset(i for i in universe if mask & (1 << i)) for mask in range(32)]

    def phase(a: frozenset[int], b: frozenset[int]) -> int:
        return len(b - a) - len(a - b)

    for a, b, c in product(subsets, repeat=3):
        assert phase(a, b) + phase(b, c) == phase(a, c)
    for h in range(1, 21):
        for n in range(-100, 101):
            assert ((n % (2 * h)) < h) != (((n + h) % (2 * h)) < h)


def main() -> None:
    print("FINITE CHECKS FOR PRIKRY FINITE SYMMETRY")
    print("No forcing or infinite-cardinal theorem is computationally verified.\n")
    checked = check_amplification()
    print(f"Amplified embeddings tau^H v = v g: {checked} cases passed.")
    print("All permutations on 1..6 labels; family-size bounds 1..5.\n")
    expected = {(2, 2, 1): (2, 2), (3, 2, 1): (8, 1), (4, 2, 1): (64, 4),
                (5, 2, 1): (1024, 1), (6, 2, 1): (32768, 2),
                (3, 3, 1): (3, 3), (3, 3, 2): (3, 3)}
    print("Selector-table cyclic orbits (orbit size: number of orbits):")
    for (N, n, r), (expected_total, expected_min) in expected.items():
        total, distribution = selector_orbits(N, n, r)
        assert total == expected_total
        assert min(distribution) == expected_min
        print(f"  N={N}, n={n}, r={r}: total={total}; "
              f"orbits={dict(sorted(distribution.items()))}; minimum={min(distribution)}")
    print("\nFive-label S3 example (permutation -> fixed labels):")
    for p, fixed in check_five_labels():
        print(f"  {p} -> {fixed}")
    print("  Intersection of all fixed-label sets: empty.")
    hist = check_periodic_word_stabilizers()
    print("\nFaithfully separating periodic incidence words, periods 1..4, 3 labels:")
    print(f"  {sum(hist.values())} words checked; stabilizer size histogram: {dict(sorted(hist.items()))}")
    print("  Every stabilizer cyclic; separation-free counterexample also checked.")
    check_phase_and_residues()
    print("\nPhase cocycle: all triples of subsets of a five-point set passed.")
    print("Half-residue complement under translation: h=1..20, n=-100..100 passed.")
    print("\nALL FINITE CHECKS PASSED.")


if __name__ == "__main__":
    main()
