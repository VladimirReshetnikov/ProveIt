"""Reproducible finite verification of the new deterministic packing routine.

Run with ordinary Python or python -O.  Every gate uses an explicit
require()/raise; optimized Python cannot disable validation.

The tests check the exact conditional-expectation construction and packet
structure.  They do not certify the full upstream SAT algorithm or establish
the asymptotic theorem by finite sampling.
"""

from __future__ import annotations

import argparse
from dataclasses import replace
from fractions import Fraction
import json
from pathlib import Path
from random import Random
import sys

from packet_packing import (
    Labeling,
    PacketPacking,
    build_oriented_packets,
    deterministic_labeling,
    label_digits,
    rational_load_bound,
    rational_padding_bound,
)


SEED = 20261026


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def _direct_conditional_potential(result: Labeling, prefix: tuple[int, ...]) -> Fraction:
    """Independently recompute the exact expectation from edge incidences.

    This intentionally does not reuse the optimized suffix products used by
    the implementation.  Each ordered-label cell is recomputed separately.
    """

    total = Fraction()
    for a in range(result.q):
        for b in range(result.q):
            fixed_load = sum(
                1
                for row, column in result.edges
                if column < len(prefix)
                and result.row_labels[row] == a
                and prefix[column] == b
            )
            cell = result.z**fixed_load
            for v in range(len(prefix), result.n_columns):
                weight = sum(
                    1 for row, column in result.edges if column == v and result.row_labels[row] == a
                )
                cell *= (result.q - 1 + result.z**weight) / result.q
            total += cell
    return total


def verify_labeling(result: Labeling) -> dict[str, int]:
    q = result.q
    require(len(result.row_labels) == result.n_rows, "wrong number of row labels")
    require(len(result.column_labels) == result.n_columns, "wrong number of column labels")
    require(all(0 <= x < q for x in result.row_labels), "invalid row label")
    require(all(0 <= x < q for x in result.column_labels), "invalid column label")

    row_degrees = [0] * result.n_rows
    column_degrees = [0] * result.n_columns
    for row, column in result.edges:
        row_degrees[row] += 1
        column_degrees[column] += 1
    require(result.delta == max([1, *row_degrees, *column_degrees]), "incorrect Delta")
    require(
        result.z == 1 + Fraction(1, result.delta * result.lambda_),
        "incorrect potential base",
    )
    greedy_loads = [0] * q
    for row, degree in enumerate(row_degrees):
        expected = min(range(q), key=lambda a: (greedy_loads[a], a))
        require(result.row_labels[row] == expected, "row assignment violates deterministic greedy rule")
        greedy_loads[expected] += degree
    require(tuple(greedy_loads) == result.row_bin_weights, "row-bin weights disagree")
    require(
        max(greedy_loads) <= Fraction(result.edge_count, q) + result.delta,
        "greedy row balance bound failed",
    )

    loads = [[0] * q for _ in range(q)]
    for row, column in result.edges:
        loads[result.row_labels[row]][result.column_labels[column]] += 1
    require(tuple(tuple(row) for row in loads) == result.loads, "load matrix disagrees with edges")
    require(sum(sum(row) for row in loads) == result.edge_count, "edge count was not preserved")
    require(result.max_load <= rational_load_bound(result), "rational maximum-load certificate failed")

    require(len(result.potential_trace) == result.n_columns + 1, "wrong potential trace length")
    prefix: tuple[int, ...] = ()
    potential = _direct_conditional_potential(result, prefix)
    require(potential == result.potential_trace[0], "incorrect initial expectation")
    checked_candidates = 0
    for v in range(result.n_columns):
        candidates = [_direct_conditional_potential(result, prefix + (b,)) for b in range(q)]
        checked_candidates += q
        require(sum(candidates, Fraction()) / q == potential, "conditional-expectation averaging identity failed")
        expected_label = min(range(q), key=lambda b: (candidates[b], b))
        require(result.column_labels[v] == expected_label, "column choice is not the specified exact minimizer")
        next_potential = candidates[expected_label]
        require(next_potential <= potential, "conditional potential increased")
        require(next_potential == result.potential_trace[v + 1], "stored potential trace disagrees")
        prefix += (expected_label,)
        potential = next_potential
    direct_terminal = sum((result.z**x for row in loads for x in row), Fraction())
    require(potential == direct_terminal, "terminal potential disagrees with direct evaluation")
    require(potential <= result.potential_trace[0], "terminal potential exceeds initial expectation")

    # Check the convexity input using only rational arithmetic at all integer
    # weights, as well as the row-weight sum on this actual graph.
    for w in range(result.delta + 1):
        require(
            result.z**w <= 1 + Fraction(w, result.delta) * (result.z**result.delta - 1),
            "secant convexity inequality failed",
        )
    return {"candidate_potentials": checked_candidates, "trace_values": len(result.potential_trace)}


def verify_packets(packing: PacketPacking) -> dict[str, int]:
    result = packing.labeling
    r, a, slots = packing.r, packing.a, packing.slots_per_packet
    require(result.q == r**a, "Q differs from r**a")
    require(slots == 2**a, "L differs from 2**a")
    h_pad = packing.common_cell_padding
    require(h_pad % slots == 0, "common padding is not divisible by L")
    require(h_pad >= result.max_load, "padding is below the maximum cell load")
    require(h_pad <= rational_padding_bound(result, slots), "rational padding certificate failed")
    require(
        len(packing.packets) * slots == h_pad * result.q**2,
        "exact packet-count identity failed",
    )

    padded_cells = [[0] * result.q for _ in range(result.q)]
    seen = [0] * result.edge_count
    row_ports = [[0] * r for _ in range(a)]
    column_ports = [[0] * r for _ in range(a)]
    real_slots = 0
    for packet in packing.packets:
        require(len(packet.coordinate_pairs) == a, "packet has wrong number of coordinates")
        require(len(packet.slots) == slots, "packet has wrong number of slots")
        for slot_index, edge_id in enumerate(packet.slots):
            row_digits: list[int] = []
            column_digits: list[int] = []
            for i, pair in enumerate(packet.coordinate_pairs):
                lo, hi = pair
                require(0 <= lo <= hi < r, "invalid unordered symbol pair")
                row_symbol = hi if (slot_index >> i) & 1 else lo
                column_symbol = lo if (slot_index >> i) & 1 else hi
                row_digits.append(row_symbol)
                column_digits.append(column_symbol)
            row_label = sum(digit * r**i for i, digit in enumerate(row_digits))
            column_label = sum(digit * r**i for i, digit in enumerate(column_digits))
            padded_cells[row_label][column_label] += 1
            if edge_id is None:
                continue
            require(0 <= edge_id < result.edge_count, "unknown edge in packet")
            seen[edge_id] += 1
            real_slots += 1
            row, column = result.edges[edge_id]
            require(result.row_labels[row] == row_label, "edge row does not follow slot orientation")
            require(result.column_labels[column] == column_label, "edge column does not follow slot orientation")
            require(label_digits(row_label, r, a) == tuple(row_digits), "row-label decoding mismatch")
            require(label_digits(column_label, r, a) == tuple(column_digits), "column-label decoding mismatch")
            for i in range(a):
                row_ports[i][row_digits[i]] += 1
                column_ports[i][column_digits[i]] += 1
    require(all(count == 1 for count in seen), "some real edge is missing or duplicated")
    require(real_slots == result.edge_count, "number of real packet slots differs from M")
    require(all(x == h_pad for row in padded_cells for x in row), "ordered label classes have unequal padding")
    port_bound = Fraction(h_pad * result.q**2, r)
    for i in range(a):
        require(sum(row_ports[i]) == result.edge_count, "row ports do not sum to M")
        require(sum(column_ports[i]) == result.edge_count, "column ports do not sum to M")
        for symbol in range(r):
            require(row_ports[i][symbol] <= port_bound, "row-symbol port bound failed")
            require(column_ports[i][symbol] <= port_bound, "column-symbol port bound failed")
            require(
                row_ports[i][symbol] + column_ports[i][symbol] <= 2 * port_bound,
                "child-wire bound failed",
            )
        d_t = slots // (2**i)
        require(
            len(packing.packets) * 2 ** (i + 1) == Fraction(2 * h_pad * result.q**2, d_t),
            "mode-family accounting identity failed",
        )
    return {"packets": len(packing.packets), "real_slots": real_slots}


def _expect_failure(action, message: str) -> None:
    try:
        action()
    except (ValueError, TypeError, RuntimeError):
        return
    raise RuntimeError(message)


def run_verification() -> dict:
    counts = {
        "edge_case_labelings": 0,
        "exhaustive_simple_graphs": 0,
        "exhaustive_labelings": 0,
        "seeded_multigraph_labelings": 0,
        "packet_labelings": 0,
        "packet_instances": 0,
        "packet_slots_checked": 0,
        "real_packet_slots_checked": 0,
        "candidate_potentials_checked": 0,
        "potential_trace_values_checked": 0,
        "determinism_checks": 0,
        "negative_controls": 0,
    }

    def check(result: Labeling) -> None:
        local = verify_labeling(result)
        counts["candidate_potentials_checked"] += local["candidate_potentials"]
        counts["potential_trace_values_checked"] += local["trace_values"]

    edge_cases = [
        (0, 0, []),
        (0, 4, []),
        (4, 0, []),
        (4, 5, []),
        (1, 1, [(0, 0)]),
        (1, 1, [(0, 0)] * 11),
        (1, 6, [(0, v) for v in range(6)]),
        (6, 1, [(u, 0) for u in range(6)]),
        (3, 3, [(u, v) for u in range(3) for v in range(3)]),
        (5, 5, [(0, 0)] * 7 + [(2, 3)] * 5 + [(4, 1)] * 3),
    ]
    for nr, nc, edges in edge_cases:
        for q in (1, 2, 3, 4):
            for lam in (1, 3):
                result = deterministic_labeling(nr, nc, edges, q, lam)
                check(result)
                counts["edge_case_labelings"] += 1

    # Every simple bipartite graph on the fixed labeled sides of size 3.
    universe = [(u, v) for u in range(3) for v in range(3)]
    for mask in range(1 << len(universe)):
        edges = [edge for index, edge in enumerate(universe) if (mask >> index) & 1]
        counts["exhaustive_simple_graphs"] += 1
        for lam in (1, 3):
            check(deterministic_labeling(3, 3, edges, 2, lam))
            counts["exhaustive_labelings"] += 1

    rng = Random(SEED)
    for case in range(180):
        nr, nc = rng.randrange(1, 7), rng.randrange(1, 7)
        edges = [
            (u, v)
            for u in range(nr)
            for v in range(nc)
            for _ in range(rng.randrange(5))
        ]
        q, lam = rng.randrange(1, 5), rng.randrange(1, 8)
        result = deterministic_labeling(nr, nc, edges, q, lam)
        check(result)
        counts["seeded_multigraph_labelings"] += 1
        if case < 24:
            require(result == deterministic_labeling(nr, nc, edges, q, lam), "repeat run was not deterministic")
            counts["determinism_checks"] += 1

    packet_examples = []
    for a in (2, 3):
        for case in range(24):
            nr, nc = rng.randrange(1, 6), rng.randrange(1, 6)
            edges = [
                (u, v)
                for u in range(nr)
                for v in range(nc)
                for _ in range(rng.randrange(4))
            ]
            result = deterministic_labeling(nr, nc, edges, 2**a, 1 + case % 5)
            check(result)
            counts["packet_labelings"] += 1
            packing = build_oriented_packets(result, 2, a)
            verified = verify_packets(packing)
            counts["packet_instances"] += 1
            counts["packet_slots_checked"] += verified["packets"] * packing.slots_per_packet
            counts["real_packet_slots_checked"] += verified["real_slots"]
            if result.edge_count >= 5 and not any(example["a"] == a for example in packet_examples):
                bound = rational_load_bound(result)
                packet_examples.append({
                    "r": 2,
                    "a": a,
                    "q": result.q,
                    "lambda": result.lambda_,
                    "edges": result.edge_count,
                    "delta": result.delta,
                    "max_load": result.max_load,
                    "common_padding": packing.common_cell_padding,
                    "packets": len(packing.packets),
                    "rational_load_bound": {"numerator": bound.numerator, "denominator": bound.denominator},
                    "potential_trace_fraction_bit_lengths": [
                        [value.numerator.bit_length(), value.denominator.bit_length()]
                        for value in result.potential_trace
                    ],
                })

    invalid_calls = [
        lambda: deterministic_labeling(-1, 1, [], 1, 1),
        lambda: deterministic_labeling(1, 1, [], 0, 1),
        lambda: deterministic_labeling(1, 1, [], 1, 0),
        lambda: deterministic_labeling(1, 1, [(1, 0)], 1, 1),
        lambda: deterministic_labeling(1, 1, [(0, -1)], 1, 1),
        lambda: deterministic_labeling(1, 1, [(0.0, 0)], 1, 1),
        lambda: deterministic_labeling(1, 1, [(0, 0, 0)], 1, 1),
        lambda: deterministic_labeling(1, 1, [], True, 1),
    ]
    for action in invalid_calls:
        _expect_failure(action, "invalid input was not rejected")
        counts["negative_controls"] += 1
    valid = deterministic_labeling(2, 2, [(0, 0), (0, 1), (1, 1)], 2, 3)
    broken_trace = replace(valid, potential_trace=(valid.potential_trace[0] + 1, *valid.potential_trace[1:]))
    _expect_failure(lambda: verify_labeling(broken_trace), "modified trace escaped validation")
    counts["negative_controls"] += 1
    changed_loads = [list(row) for row in valid.loads]
    changed_loads[0][0] += 1
    broken_loads = replace(valid, loads=tuple(tuple(row) for row in changed_loads))
    _expect_failure(lambda: verify_labeling(broken_loads), "modified loads escaped validation")
    counts["negative_controls"] += 1
    _expect_failure(lambda: build_oriented_packets(valid, 2, 2), "mismatched packet alphabet escaped validation")
    counts["negative_controls"] += 1
    packet_control = build_oriented_packets(
        deterministic_labeling(2, 2, [(0, 0), (0, 1), (1, 1)], 4, 3), 2, 2
    )
    packet_index = next(
        index for index, packet in enumerate(packet_control.packets)
        if any(edge_id is not None for edge_id in packet.slots)
    )
    original_packet = packet_control.packets[packet_index]
    slot_index = next(index for index, edge_id in enumerate(original_packet.slots) if edge_id is not None)
    removed_slots = list(original_packet.slots)
    removed_slots[slot_index] = None
    altered_packets = list(packet_control.packets)
    altered_packets[packet_index] = replace(original_packet, slots=tuple(removed_slots))
    _expect_failure(
        lambda: verify_packets(replace(packet_control, packets=tuple(altered_packets))),
        "deleted packet edge escaped validation",
    )
    counts["negative_controls"] += 1
    altered_pairs = list(original_packet.coordinate_pairs)
    altered_pairs[0] = (1, 1) if altered_pairs[0] == (0, 0) else (0, 0)
    altered_packets[packet_index] = replace(original_packet, coordinate_pairs=tuple(altered_pairs))
    _expect_failure(
        lambda: verify_packets(replace(packet_control, packets=tuple(altered_packets))),
        "corrupted packet orientation escaped validation",
    )
    counts["negative_controls"] += 1

    total_labelings = sum(counts[key] for key in (
        "edge_case_labelings", "exhaustive_labelings", "seeded_multigraph_labelings", "packet_labelings"
    ))
    require(counts["exhaustive_simple_graphs"] == 512, "exhaustive graph coverage is incomplete")
    require(counts["exhaustive_labelings"] == 1024, "exhaustive lambda coverage is incomplete")
    require(counts["packet_instances"] == 48, "packet test coverage is incomplete")
    return {
        "status": "PASS",
        "python_optimization_level": sys.flags.optimize,
        "seed": SEED,
        "arithmetic": "fractions.Fraction; exact comparisons and integer log majorants",
        "total_labelings_verified": total_labelings,
        "counts": counts,
        "packet_examples": packet_examples,
        "checks": [
            "deterministic weighted-greedy row assignment and balance",
            "direct recomputation of every stored conditional expectation",
            "exact averaging identity over every next-label choice",
            "chosen label is the exact minimum with deterministic tie breaking",
            "nonincreasing potential and exact terminal potential",
            "load matrix and all parallel-edge multiplicities preserved",
            "rational conservative load and padding certificates",
            "secant convexity inequality at every integer weight up to Delta",
            "exact common padding and packet count",
            "all real edges appear exactly once in matching row/column slots",
            "slot bits implement every coordinate orientation",
            "coordinate-symbol port bounds, child-wire bounds, and mode-family identity",
            "invalid inputs, corrupted trace/loads, deleted edge, and corrupted orientation are detected",
        ],
        "scope": "Finite tests of the new packing construction; not an end-to-end SAT solver or a finite-test proof of the asymptotic theorem.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output", type=Path,
        default=Path(__file__).resolve().parents[1] / "results" / "packing_checks.json",
    )
    args = parser.parse_args()
    summary = run_verification()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": summary["status"],
        "labelings": summary["total_labelings_verified"],
        "exhaustive_graphs": summary["counts"]["exhaustive_simple_graphs"],
        "packet_instances": summary["counts"]["packet_instances"],
        "negative_controls": summary["counts"]["negative_controls"],
        "optimization_level": summary["python_optimization_level"],
        "output": str(args.output.resolve()),
    }, indent=2))


if __name__ == "__main__":
    main()
