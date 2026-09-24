#!/usr/bin/env python3
"""Exact finite diagnostics for sparse-error minimal-pair forcing.

These are checks of finite combinatorial statements, NOT a computation of the
noncomputable sets in the report and NOT a formal verification of its proof.
Requires Python 3.10+ and only the standard library.
"""
from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from random import Random
from typing import Callable, Iterable

Bits = tuple[int, ...]
Weight = Callable[[int], Fraction]


def words(length: int) -> list[Bits]:
    if length < 0:
        raise ValueError("length must be nonnegative")
    return list(itertools.product((0, 1), repeat=length))


def cost(left: Bits, right: Bits, weight: Weight) -> Fraction:
    if len(left) != len(right):
        raise ValueError("stems must have equal length")
    if any(bit not in (0, 1) for bit in left + right):
        raise ValueError("stems must be binary")
    return sum((weight(n) for n, (a, b) in enumerate(zip(left, right))
                if a != b), Fraction(0))


def bridge_graph(tail_length: int) -> tuple[list[tuple[int, int]], int]:
    """Legal bipartite pairs above stems costing 1/3, with budget 1/2."""
    weight = lambda n: Fraction(1, n + 1)
    sigma = (0,) * 6
    tau = (0, 0, 1, 0, 0, 0)
    tails = words(tail_length)
    m = len(tails)
    edges = [(i, m + j) for i, a in enumerate(tails)
             for j, b in enumerate(tails)
             if cost(sigma + a, tau + b, weight) < Fraction(1, 2)]
    adjacency: list[list[int]] = [[] for _ in range(2 * m)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    assert len(seen) == 2 * m
    edge_set = set(edges)
    for i, a in enumerate(tails):
        assert (i, m + i) in edge_set
        for j, b in enumerate(tails):
            if sum(x != y for x, y in zip(a, b)) == 1:
                assert (i, m + j) in edge_set
    return edges, 2 * m


def exhaustive_boolean_label_check() -> dict[str, int]:
    edges, size = bridge_graph(3)
    valid = []
    for labeling in range(1 << size):
        if all(((labeling >> u) & 1) == ((labeling >> v) & 1)
               for u, v in edges):
            valid.append(labeling)
    assert valid == [0, (1 << size) - 1]
    return {"vertices": size, "edges": len(edges),
            "labelings_checked": 1 << size, "consistent_labelings": len(valid)}


def disconnected_partial_domain_check() -> dict[str, object]:
    """No splitting does not force constancy without a density hypothesis."""
    domain = {(0, 0, 0): 0, (1, 1, 1): 1}
    legal = [(a, b) for a in domain for b in domain
             if sum(x != y for x, y in zip(a, b)) <= 1]
    assert len(legal) == 2
    assert all(domain[a] == domain[b] for a, b in legal)
    assert len(set(domain.values())) == 2
    return {"domain": {"".join(map(str, k)): v for k, v in domain.items()},
            "legal_pairs": len(legal), "constant": False,
            "lesson": "density of convergence domains is essential"}


def copy_extension_checks() -> int:
    weight = lambda n: Fraction(1, n + 1)
    count = 0
    for length in range(5):
        for sigma in words(length):
            for tau in words(length):
                original = cost(sigma, tau, weight)
                for suffix in words(3):
                    assert cost(sigma + suffix, tau + suffix, weight) == original
                    count += 1
    return count


def padding_checks() -> int:
    rng = Random(20260918)
    count = 0
    for _ in range(300):
        length = rng.randrange(0, 15)
        sigma = tuple(rng.randrange(2) for _ in range(length))
        tau = tuple(rng.randrange(2) for _ in range(length))
        c = cost(sigma, tau, lambda n: Fraction(1, n + 1))
        slack = Fraction(1, rng.randrange(1, 30))
        budget = c + slack
        L = length
        while c + Fraction(1, L + 1) >= budget:
            L += 1
        for offset in range(7):
            position = L + offset
            left = sigma + (0,) * (position + 1 - length)
            right = tau + (0,) * (position - length) + (1,)
            assert cost(left, right, lambda n: Fraction(1, n + 1)) < budget
            count += 1
    return count


def finite_tail_inequality_checks() -> int:
    rng = Random(250806925)
    orders: list[Callable[[int], int]] = [
        lambda n: n + 1,
        lambda n: (n + 1).bit_length(),
        lambda n: ((n + 1).bit_length()).bit_length(),
    ]
    count = 0
    for h in orders:
        for _ in range(300):
            N = rng.randrange(1, 200)
            M = rng.randrange(N + 1)
            E = {n for n in range(N + 30) if rng.randrange(7) == 0}
            lhs = Fraction(len(E.intersection(range(N))), h(N))
            rhs = Fraction(M, h(N)) + sum(
                (Fraction(1, h(n)) for n in E if n >= M), Fraction(0))
            assert lhs <= rhs
            count += 1
    return count


def dyadic_majority_checks() -> int:
    count = 0
    for n in range(4):
        block_length = 1 << n
        endpoint = 2 * block_length
        for true_bit in (0, 1):
            for block in words(block_length):
                decoded = int(sum(block) > block_length // 2)
                if decoded != true_bit:
                    errors = sum(bit != true_bit for bit in block)
                    # Earlier positions may have further errors, never fewer.
                    assert Fraction(errors, endpoint) >= Fraction(1, 4)
                count += 1
    return count


def simultaneous_suffix_checks() -> dict[str, int]:
    """A finite model of meeting many open dense convergence domains.

Every supplied domain accepts a string once a designated bit-pattern occurs
anywhere. Appending the patterns successively preserves all earlier witnesses.
This illustrates suffix synchronization, not arbitrary c.e. domain density.
"""
    patterns = words(1) + words(2) + words(3)
    suffix: Bits = ()
    for pattern in patterns:
        suffix += pattern
    for pattern in patterns:
        assert any(suffix[i:i + len(pattern)] == pattern
                   for i in range(len(suffix) - len(pattern) + 1))
    return {"dense_open_toy_domains": len(patterns),
            "common_suffix_length": len(suffix)}


def run_checks() -> dict[str, object]:
    graph_sizes = []
    for n in range(1, 7):
        edges, vertices = bridge_graph(n)
        graph_sizes.append({"tail_length": n, "vertices": vertices,
                            "edges": len(edges), "connected": True})
    return {
        "status": "all finite checks passed",
        "scope": "Finite diagnostics only; no infinite construction or Lean verification.",
        "arithmetic": "exact fractions; no floating-point acceptance thresholds",
        "bridge_graphs": graph_sizes,
        "exhaustive_boolean_labels": exhaustive_boolean_label_check(),
        "partial_domain_counterexample": disconnected_partial_domain_check(),
        "copy_extensions_checked": copy_extension_checks(),
        "one_bit_padding_checks": padding_checks(),
        "finite_tail_inequalities_checked": finite_tail_inequality_checks(),
        "dyadic_majority_cases_checked": dyadic_majority_checks(),
        "simultaneous_suffix_toy_check": simultaneous_suffix_checks(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("finite_checks_results.json"))
    args = parser.parse_args()
    results = run_checks()
    args.output.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
