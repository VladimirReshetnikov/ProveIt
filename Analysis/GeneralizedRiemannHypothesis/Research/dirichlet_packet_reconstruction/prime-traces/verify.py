#!/usr/bin/env python3
"""Finite checks of the prime-trace theorems. Run with Python 3.10 or later."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import gcd


def walsh(label, point):
    return -1 if (label & point).bit_count() % 2 else 1


def near_spectrum(rank, size):
    degree = (2 * size).bit_length() - 1
    if rank <= degree:
        return {Fraction(1, 2**rank)}
    return {
        Fraction(2**index - 1, 2 ** (degree + index - 1))
        for index in range(1, min(degree, rank - degree) + 1)
        if size >= 2**degree - 2 ** (degree - index)
    }


def check_extremizer(diff, rank, degree):
    support = [point for point, value in enumerate(diff) if value]
    base = support[0]
    assert base != 0
    if rank <= degree:
        assert len(support) == 1
        assert diff[base] % (1 << rank) == 0
        return
    shifted = {x ^ base for x in support}
    assert all(x ^ y in shifted for x in shifted for y in shifted)
    assert abs(diff[base]) == 1 << degree
    assert any(
        all(diff[x] == diff[base] * walsh(label, x ^ base) for x in support)
        for label in range(1 << rank)
    )


def exhaustive(rank, size):
    labels = range(1 << rank)
    characters = [[walsh(label, x) for x in labels] for label in labels]
    packets = list(combinations_with_replacement(labels, size))
    traces = [
        tuple(map(sum, zip(*(characters[label] for label in packet))))
        for packet in packets
    ]
    degree = (2 * size).bit_length() - 1
    minimum = Fraction(1, 1 << min(rank, degree))
    spectrum = set()
    pair_count = 0
    for i, j in combinations(range(len(packets)), 2):
        pair_count += 1
        weight = sum(a != b for a, b in zip(traces[i], traces[j]))
        density = Fraction(weight, 1 << rank)
        assert density >= minimum
        if density >= 2 * minimum:
            continue
        spectrum.add(density)
        if rank > degree:
            c = Counter(packets[i])
            c.subtract(packets[j])
            assert all(abs(mult) <= 1 for mult in c.values())
            assert sum(abs(mult) for mult in c.values()) == 4**degree * density
        if density == minimum:
            check_extremizer(
                [a - b for a, b in zip(traces[i], traces[j])], rank, degree
            )
    assert spectrum == near_spectrum(rank, size), (rank, size, spectrum)
    print(f"r={rank} k={size}: {pair_count:>7} pairs; "
          + ", ".join(map(str, sorted(spectrum))))
    return pair_count


def subspace(indices):
    values = {0}
    for index in indices:
        values |= {x ^ (1 << index) for x in values}
    return values


def witness(rank, degree, index):
    common = list(range(degree - index))
    left = subspace(list(range(degree)))
    right = subspace(common + list(range(degree, degree + index)))
    packet_a, packet_b = left - right, right - left
    assert len(packet_a) == len(packet_b) == 2**degree - 2 ** (degree - index)
    left_mask = sum(1 << x for x in range(degree))
    right_mask = sum(1 << x for x in common + list(range(degree, degree + index)))
    support_size = 0
    for point in range(1 << rank):
        diff = sum(walsh(label, point) for label in packet_a)
        diff -= sum(walsh(label, point) for label in packet_b)
        assert diff == (1 << degree) * (
            int((point & left_mask) == 0) - int((point & right_mask) == 0)
        )
        support_size += bool(diff)
    expected = Fraction(2**index - 1, 2 ** (degree + index - 1))
    assert Fraction(support_size, 1 << rank) == expected


def residue_example():
    factors = (3, 5, 7, 11)
    modulus = 3 * 5 * 7 * 11
    left = {1, 2, 3}       # Nontrivial members of span(e0,e1)
    right = {4, 8, 12}     # Nontrivial members of span(e2,e3)
    disagreements = units = 0
    for a in range(modulus):
        if gcd(a, modulus) != 1:
            continue
        units += 1
        point = sum(
            (1 << pos)
            for pos, prime in enumerate(factors)
            if pow(a, (prime - 1) // 2, prime) == prime - 1
        )
        disagreements += (
            sum(walsh(label, point) for label in left)
            != sum(walsh(label, point) for label in right)
        )
    assert Fraction(disagreements, units) == Fraction(3, 8)
    print(f"Q={modulus}: {disagreements}/{units} reduced classes disagree (3/8).")


if __name__ == "__main__":
    total = sum(
        exhaustive(rank, size)
        for rank, max_size in [(1, 6), (2, 6), (3, 5), (4, 3)]
        for size in range(1, max_size + 1)
    )
    print(f"All {total} unordered pairs passed, including extremal structure.")
    count = 0
    for rank in range(2, 11):
        for degree in range(1, rank):
            for index in range(1, min(degree, rank - degree) + 1):
                witness(rank, degree, index)
                count += 1
    print(f"All {count} subspace constructions passed through rank 10.")
    residue_example()
