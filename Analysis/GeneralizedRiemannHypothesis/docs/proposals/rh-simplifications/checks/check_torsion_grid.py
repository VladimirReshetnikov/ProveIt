#!/usr/bin/env python3
"""Exact checks for the cyclotomic grid and its interpolation inequality.

A node (h,a) denotes xi_h**a-1 for one primitive ell**h-th root xi_h
per level. All quantities are normalized additive valuations or integers.
The bad-set examples use polynomials with several roots in the same shell.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import inf


@dataclass(frozen=True)
class Node:
    level: int
    exponent: int


def radius(prime, level):
    return Fraction(1, prime ** (level - 1) * (prime - 1))


def difference(prime, left, right):
    """Valuation of the difference, from the exact order of a cyclotomic root."""
    if left == right:
        return inf
    if left.level != right.level:
        return min(radius(prime, node.level) for node in (left, right))
    exponent = abs(left.exponent - right.exponent)
    order_level = left.level
    while exponent % prime == 0:
        exponent //= prime
        order_level -= 1
    return radius(prime, order_level)


def grid(prime, levels, delta, inner_radius):
    nodes = []
    for level in levels:
        weight = radius(prime, level)
        if weight >= inner_radius:
            continue
        cutoff = int(delta / (4 * (level + 1) * weight))
        shell = [Node(level, a) for a in range(1, cutoff + 1) if a % prime]
        for node in shell:
            assert sum(difference(prime, node, other)
                       for other in shell if node != other) <= delta / 2
        nodes.extend(shell)
    return nodes


def check_capacity(prime, levels):
    delta = Fraction(1, 2)
    nodes = grid(prime, levels, delta, Fraction(1, 3))
    assert len(nodes) >= 7
    # Given v(y) greater than each node's valuation, v(y-node)=v(node).
    sample = nodes[:7]
    some_negative = False
    for size in range(1, len(sample) + 1):
        for subset in combinations(sample, size):
            for node in subset:
                weight = sum(radius(prime, other.level) - difference(prime, node, other)
                             for other in subset if other != node)
                assert weight >= -delta / 2
                some_negative |= weight < 0
    # Also check same-level pairs with exponents differing by a multiple of ell.
    for node in nodes:
        for other in nodes:
            if node == other:
                continue
            quotient = radius(prime, other.level) - difference(prime, node, other)
            some_negative |= quotient < 0
            assert quotient >= -delta / 2
    assert some_negative
    examples = 0
    # g(T) = product over c in roots of (T-c); reference y=0.
    for degree in (1, 2, 3, 4):
        for roots in combinations(sample, degree):
            reference = sum(radius(prime, root.level) for root in roots)
            bad = [node for node in nodes
                   if sum(difference(prime, node, root) for root in roots) > reference + delta]
            assert set(roots) == set(bad)
            assert sum(radius(prime, node.level) for node in bad) <= reference
            examples += 1
    print(f"ell={prime}: {len(nodes)} grid points, 127 interpolation subsets, "
          f"{examples} bad-set checks passed.")


if __name__ == '__main__':
    check_capacity(2, range(4, 12))
    check_capacity(3, range(2, 8))
