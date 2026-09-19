#!/usr/bin/env python3
"""Finite bookkeeping checks for Prikry Choice and Maximal Rigidity.

These tests do NOT verify forcing arguments, infinite cardinal claims, HOD,
or infinite ultrafilters. They check finite identities used by the English
proofs. Standard library only; Python 3.10 or later.
"""
from __future__ import annotations

from itertools import combinations, permutations, product
from math import lcm
import json


def require(condition: bool, message: str) -> None:
    """Unlike a bare assert, this check also runs under python -O."""
    if not condition:
        raise AssertionError(message)


def inverse(p: tuple[int, ...]) -> tuple[int, ...]:
    result = [0] * len(p)
    for i, j in enumerate(p):
        result[j] = i
    return tuple(result)


def iterate(p: tuple[int, ...], i: int, n: int) -> int:
    for _ in range(n):
        i = p[i]
    return i


def check_twisted_deletion() -> dict[str, int]:
    """A finite block coordinate replaces the ordinal block omega * c_n."""
    c = tuple(7 + 5 * n for n in range(12))
    cases = 0
    perms = 0
    for m in range(1, 6):
        for p in permutations(range(m)):
            perms += 1
            pinv = inverse(p)
            for k in range(len(c) - 1):
                d = c[:k] + c[k + 1:]
                for i in range(m):
                    for n in range(k, len(d)):
                        left = (d[n], iterate(p, i, n))
                        right = (c[n + 1], iterate(p, pinv[i], n + 1))
                        require(left == right, f"Twist failure: {p}, {k}, {i}, {n}")
                        cases += 1
    return {"permutations": perms, "point_identities": cases}


def all_subsets(n: int) -> list[frozenset[int]]:
    return [frozenset(c) for r in range(n + 1) for c in combinations(range(n), r)]


def index(a: frozenset[int], b: frozenset[int]) -> int:
    return len(b - a) - len(a - b)


def check_phase() -> dict[str, int]:
    subsets = all_subsets(6)
    cases = 0
    for a in subsets:
        for gamma in a:
            d = a - {gamma}
            for b in subsets:
                require(index(d, b) == index(a, b) + 1, "Phase deletion failure")
                cases += 1
    residue_cases = 0
    for m in range(2, 10):
        for mask in range(1, (1 << m) - 1):
            r = {i for i in range(m) if mask & (1 << i)}
            require({(i + 1) % m for i in r} != r, "A proper phase set is invariant")
            residue_cases += 1
    return {"integer_phase_identities": cases, "proper_residue_sets": residue_cases}


def shift_subset(b: tuple[int, ...], n: int, step: int = 1) -> tuple[int, ...]:
    return tuple(sorted((i + step) % n for i in b))


def check_small_table_orbits() -> dict[str, int]:
    """Enumerate all tables in small cases and compute their full cycle orbits."""
    parameters = [(n, r, 1) for n in range(2, 6) for r in range(1, n)]
    parameters.append((2, 1, 2))
    table_count = 0
    orbit_count = 0
    for n, r, k in parameters:
        length = lcm(*range(1, k + 1))
        size = n * length
        inputs = list(combinations(range(size), n))
        input_index = {b: i for i, b in enumerate(inputs)}
        choices = [list(combinations(b, r)) for b in inputs]
        tables = set(product(*choices))
        table_count += len(tables)

        def act(table: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
            # (tau t)(B) = tau[t(tau^{-1}[B])].
            return tuple(
                shift_subset(table[input_index[shift_subset(b, size, -1)]], size)
                for b in inputs
            )

        unseen = set(tables)
        while unseen:
            first = min(unseen)
            orbit = {first}
            current = act(first)
            while current != first:
                require(current not in orbit, "Cycle returned to a noninitial table")
                orbit.add(current)
                current = act(current)
            require(len(orbit) > k, f"Short table orbit for {(n, r, k)}")
            unseen.difference_update(orbit)
            orbit_count += 1
    return {"parameter_triples": len(parameters), "tables": table_count, "orbits": orbit_count}


def fixed_table_exists(size: int, n: int, r: int, step: int) -> bool:
    """Exact orbit-constraint test for a table fixed by the indicated cycle power.

    On each orbit of n-subsets, choose the value on one subset. After returning
    to that subset, its r-subset value must be fixed by the return permutation.
    Distinct input orbits impose independent constraints. No whole-table
    enumeration is needed.
    """
    unseen = set(combinations(range(size), n))
    while unseen:
        base = min(unseen)
        orbit = [base]
        current = shift_subset(base, size, step)
        while current != base:
            orbit.append(current)
            current = shift_subset(current, size, step)
        unseen.difference_update(orbit)
        return_step = step * len(orbit)
        if not any(shift_subset(v, size, return_step) == v for v in combinations(base, r)):
            return False
    return True


def check_table_constraints() -> dict[str, int]:
    cases = 0
    for n in range(2, 5):
        for r in range(1, n):
            for k in range(1, 4):
                size = n * lcm(*range(1, k + 1))
                for step in range(1, k + 1):
                    require(
                        not fixed_table_exists(size, n, r, step),
                        f"Fixed table for {(size, n, r, k, step)}",
                    )
                    cases += 1
    return {"exact_orbit_constraint_tests": cases}


def binary_code(node: tuple[int, ...]) -> int:
    value = 0
    for bit in node:
        value = 2 * value + bit
    return (1 << len(node)) - 1 + value


def check_tree() -> dict[str, int]:
    depth = 8
    nodes = [node for level in range(depth + 1) for node in product((0, 1), repeat=level)]
    codes = [binary_code(node) for node in nodes]
    require(len(codes) == len(set(codes)), "Noninjective tree code")
    for node in nodes:
        require(binary_code(node) >= len(node), "A node code lies below its level")
    for level in range(depth):
        last = max(binary_code(t) for t in product((0, 1), repeat=level))
        first_next = min(binary_code(t) for t in product((0, 1), repeat=level + 1))
        require(last < first_next, "Tree levels overlap")
    branches = list(product((0, 1), repeat=depth))
    sample_levels = (0, 2, 4, 6, 8)
    pairs = 0
    for x, y in combinations(branches, 2):
        first_difference = next(i for i in range(depth) if x[i] != y[i])
        xs = {binary_code(x[:n]) for n in sample_levels}
        ys = {binary_code(y[:n]) for n in sample_levels}
        allowed = {binary_code(x[:n]) for n in sample_levels if n <= first_difference}
        require(xs & ys == allowed, "Branch-code overlap after first difference")
        pairs += 1
    return {"tree_nodes": len(nodes), "branches": len(branches), "branch_pairs": pairs}


def main() -> None:
    results = {
        "status": "PASS",
        "scope": "finite bookkeeping only; not formal verification of set theory",
        "twisted_deletion": check_twisted_deletion(),
        "phase_partitions": check_phase(),
        "enumerated_selector_tables": check_small_table_orbits(),
        "selector_orbit_constraints": check_table_constraints(),
        "binary_tree_codes": check_tree(),
    }
    print(json.dumps(results, indent=2))


if __name__ == "__main__":
    main()
