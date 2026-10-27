"""Deterministic semantic and structural tests for equality_normalization.

Run: python3 verify_normalization.py --output normalization_results.json
Only the standard library is required. No end-to-end subexponential solver
or performance benchmark is supplied or claimed by these tests.
"""

from __future__ import annotations

import argparse
from dataclasses import replace
from itertools import product
import json
from pathlib import Path
import random

from equality_normalization import (
    Formula, build_network, count_formula_bruteforce, count_network_bruteforce,
    normalize_3cnf,
)


def require(condition: bool, details=None) -> None:
    """Checks remain active even when Python is run with -O."""

    if not condition:
        raise AssertionError(details)


def raw_count(n: int, clauses: list[tuple[int, ...]]) -> int:
    """Independent Boolean oracle evaluating the unnormalized input."""

    result = 0
    for mask in range(1 << n):
        accepted = True
        for clause in clauses:
            satisfied = False
            for literal in clause:
                bit = (mask >> (abs(literal) - 1)) & 1
                if (literal > 0 and bit == 1) or (literal < 0 and bit == 0):
                    satisfied = True
                    break
            if not satisfied:
                accepted = False
                break
        result += int(accepted)
    return result


def gadget_extensions(degree: int, cap: int) -> tuple[int, int]:
    """Exhaust all boundary/internal bits and verify unique extension.

    Distinct clauses (x_1 or x_j) expose the desired x_1 gadget. Only its
    equality nodes are evaluated, so all 2^degree boundary conditions are
    tested independently of the other variables and clause tensors.
    """

    formula = normalize_3cnf(degree + 1, [(1, j + 2) for j in range(degree)])
    network = build_network(formula, cap)
    external = [i for i, wire in enumerate(network.wires)
                if wire.variable == 1 and not wire.internal]
    internal = [i for i, wire in enumerate(network.wires)
                if wire.variable == 1 and wire.internal]
    ordered_edges = external + internal
    positions = {edge: position for position, edge in enumerate(ordered_edges)}
    local_ports = [tuple(positions[edge] for edge in tensor.edges)
                   for tensor in network.tensors
                   if tensor.kind == "equality" and tensor.variable == 1]
    counts = [0] * (1 << degree)
    mask_boundary = (1 << degree) - 1
    checked = 1 << len(ordered_edges)
    for mask in range(checked):
        legal = True
        for ports in local_ports:
            bit = (mask >> ports[0]) & 1
            if any(((mask >> port) & 1) != bit for port in ports[1:]):
                legal = False
                break
        if legal:
            counts[mask & mask_boundary] += 1
    expected = [0] * (1 << degree)
    expected[0] = 1
    expected[-1] = 1
    require(counts == expected, (degree, cap, counts))
    return checked, len(counts)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rng = random.Random(20261026)

    # Includes both counting conventions at zero variables, tautologies,
    # repeated literals/clauses, opposite signs, unused variables, and mixed
    # clause widths. Empty clauses are tested without silently discarding them.
    fixtures: list[tuple[int, list[tuple[int, ...]]]] = [
        (0, []), (0, [()]), (4, []), (3, [(1,)]),
        (3, [(-1,)]), (2, [(1,), (-1,)]),
        (3, [(1, -1, 2), (2, 2, 3), (2, 3)]),
        (5, [(1, 1, 1), (-2, 3), (-2, 3), (1, -3, 4)]),
        (4, [(), (1, -2, 3)]),
        (5, [(1, 2), (1, 3), (1, 4), (1, 5)]),
        (5, [(-1, 2), (1, -3), (-1, 4), (1, -5)]),
    ]
    for _ in range(160):
        n = rng.randrange(1, 6)
        clauses: list[tuple[int, ...]] = []
        for _ in range(rng.randrange(1, 8)):
            width = rng.choice((1, 2, 2, 3, 3, 3))
            clauses.append(tuple(rng.choice((-1, 1)) * rng.randrange(1, n + 1)
                                 for _ in range(width)))
        if rng.randrange(17) == 0:
            clauses.append(())
        fixtures.append((n, clauses))

    network_fixtures = 0
    wire_contractions = 0
    variable_assignments = 0
    wire_assignments = 0
    largest_network = 0
    for n, clauses in fixtures:
        original = raw_count(n, clauses)
        formula = normalize_3cnf(n, clauses)
        require(count_formula_bruteforce(formula) == original)
        for cap in (3, 4, 5, 8):
            network = build_network(formula, cap)
            network.validate()
            network_fixtures += 1
            largest_network = max(largest_network, len(network.wires))
            L = formula.literal_count
            require(len(network.wires) * (cap - 2) <= L * cap)
            # Validate each original assignment's contribution using the unique
            # consistent extension, without invoking the formula evaluator.
            contribution_count = 0
            for bits in product((0, 1), repeat=n):
                edge_bits = tuple(bits[wire.variable - 1] for wire in network.wires)
                contribution_count += network.weight(edge_bits)
                variable_assignments += 1
            require(contribution_count == original)
            if len(network.wires) <= 14:
                actual = count_network_bruteforce(network, max_wires=14)
                require(actual == original, (n, clauses, cap, actual, original))
                wire_contractions += 1
                wire_assignments += 1 << len(network.wires)

    gadget_cases = 0
    gadget_bit_assignments = 0
    gadget_boundary_conditions = 0
    for degree in range(1, 9):
        for cap in range(3, 8):
            checked, boundaries = gadget_extensions(degree, cap)
            gadget_cases += 1
            gadget_bit_assignments += checked
            gadget_boundary_conditions += boundaries

    # Structural size checks include large gadgets, but never expand tensor
    # tables or enumerate their Boolean assignments.
    structural_cases = 0
    structural_max_wires = 0
    for degree in (9, 17, 64, 257, 1000):
        formula = normalize_3cnf(degree + 1, [(1, j + 2) for j in range(degree)])
        for cap in (3, 4, 7, 16, 63):
            network = build_network(formula, cap)
            require(len(network.wires) == 2 * degree + 2 * (max(degree - 3, 0) // (cap - 2)))
            # Parentheses matter in the theoretical formula; independently
            # inspect the number of subdivision vertices as well.
            subdivisions = sum(t.kind == "equality" and t.side == 0 for t in network.tensors)
            require(subdivisions == max(degree - 3, 0) // (cap - 2))
            structural_cases += 1
            structural_max_wires = max(structural_max_wires, len(network.wires))

    # Deliberately wrong sign: the contradictory pair becomes x AND x.
    contradiction = build_network(normalize_3cnf(1, [(1,), (-1,)]), 3)
    mutated = tuple(replace(t, signs=(True,)) if t.kind == "clause" else t
                    for t in contradiction.tensors)
    wrong_sign_network = replace(contradiction, tensors=mutated)
    wrong_sign_detected = count_network_bruteforce(wrong_sign_network) != 0
    require(wrong_sign_detected)

    # Deliberately broken equality: accepting inconsistent occurrence bits
    # creates a false solution to the same contradictory formula.
    equal_node = next(t.index for t in contradiction.tensors if t.kind == "equality")
    broken_count = 0
    for bits in product((0, 1), repeat=len(contradiction.wires)):
        broken_count += int(all(
            t.index == equal_node or t.entry(tuple(bits[e] for e in t.edges))
            for t in contradiction.tensors
        ))
    broken_equality_detected = broken_count != 0
    require(broken_equality_detected)

    invalid_cases = [
        lambda: normalize_3cnf(-1, []),
        lambda: normalize_3cnf(2, [(0,)]),
        lambda: normalize_3cnf(2, [(3,)]),
        lambda: normalize_3cnf(2, [(True,)]),
        lambda: normalize_3cnf(2, [(1, 1, 1, 1)]),
        lambda: build_network(normalize_3cnf(1, [(1,)]), 2),
        lambda: build_network(Formula(1, ((1, 1),)), 3),
        lambda: count_network_bruteforce(contradiction, max_wires=0),
    ]
    invalid_rejections = 0
    for invalid in invalid_cases:
        try:
            invalid()
        except ValueError:
            invalid_rejections += 1
        else:
            raise AssertionError("invalid input was accepted")

    results = {
        "status": "passed",
        "seed": 20261026,
        "raw_formula_fixtures": len(fixtures),
        "network_fixtures": network_fixtures,
        "original_variable_assignments_checked": variable_assignments,
        "full_integer_tensor_contractions": wire_contractions,
        "wire_assignments_in_full_contractions": wire_assignments,
        "largest_random_network_wires": largest_network,
        "equality_gadget_cases": gadget_cases,
        "equality_boundary_conditions": gadget_boundary_conditions,
        "equality_boundary_and_internal_assignments": gadget_bit_assignments,
        "large_structural_cases": structural_cases,
        "largest_structural_network_wires": structural_max_wires,
        "negative_controls": {
            "wrong_literal_sign_detected": wrong_sign_detected,
            "broken_equality_detected": broken_equality_detected,
        },
        "invalid_inputs_rejected": invalid_rejections,
        "scope": "Exact normalization and finite semantic checks; no subexponential contractor implemented.",
    }
    rendered = json.dumps(results, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")


if __name__ == "__main__":
    main()
