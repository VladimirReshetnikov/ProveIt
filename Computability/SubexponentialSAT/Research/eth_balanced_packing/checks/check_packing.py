#!/usr/bin/env python3
"""Independent exhaustive checks for the exact balanced-packing prototype.

Run from any directory.  The tiny graphs are certified directly through the
exact initial potential; they need not satisfy asymptotic size inequalities.
The checks remain active under python -O and do not import external programs.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from random import Random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'code'))
from packing import (Graph, asymptotic_parameters, certified_threshold,
                     conditional_potential, derandomize_columns,
                     greedy_row_labels, label_digits, make_packets,
                     row_group_weights)


COUNTS = Counter()


def require(condition: bool, label: str) -> None:
    if not condition:
        raise RuntimeError(label)
    COUNTS[label] += 1


def exhaustive_potential(weights, groups, z, threshold, prefix):
    """Independent enumeration: construct every cell load from scratch."""
    columns = len(weights[0])
    total = Fraction(0)
    completions = 0
    for suffix in product(range(groups), repeat=columns - len(prefix)):
        labels = tuple(prefix) + suffix
        cells = [[0] * groups for _ in range(groups)]
        for row_group in range(groups):
            for vertex in range(columns):
                cells[row_group][labels[vertex]] += weights[row_group][vertex]
        total += sum((z ** (load - threshold) for row in cells for load in row), Fraction(0))
        completions += 1
    COUNTS['exhaustive_label_completions'] += completions
    return total / completions


def graph_cases():
    cases = [
        ('empty', Graph(0, 0, ())),
        ('isolated_vertices', Graph(3, 4, ((0, 0), (2, 3)))),
        ('parallel_edges', Graph(2, 3, ((0, 0),) * 5 + ((1, 0),) * 2 + ((1, 1),))),
        ('asymmetric', Graph(6, 2, tuple((i, i % 2) for i in range(6)))),
        ('star', Graph(1, 4, ((0, 0), (0, 1), (0, 2), (0, 3)))),
        ('column_star', Graph(4, 1, ((0, 0), (1, 0), (2, 0), (3, 0)))),
    ]
    rng = Random(20261026)
    for index in range(34):
        left = 1 + index % 5
        right = index % 5
        edges = tuple((rng.randrange(left), rng.randrange(right))
                      for _ in range(index % 13)) if right else ()
        cases.append((f'generated_{index:02d}', Graph(left, right, edges)))
    return cases


def check_graph(name, graph, groups, z):
    row_labels, row_loads = greedy_row_labels(graph, groups)
    require(sum(row_loads) == graph.size, 'greedy_mass_conservation')
    require(max(row_loads, default=0) * groups <= graph.size + groups * graph.max_degree,
            'greedy_row_balance')
    require((row_labels, row_loads) == greedy_row_labels(graph, groups), 'deterministic_row_labels')
    weights = row_group_weights(graph, row_labels, groups)
    require(sum(map(sum, weights)) == graph.size, 'weight_mass_conservation')
    require(all(weight <= graph.max_degree for row in weights for weight in row), 'bounded_column_weights')
    threshold = certified_threshold(weights, groups, z)
    initial = conditional_potential(weights, groups, z, threshold)
    require(initial < 1, 'strict_initial_certificate')
    if threshold:
        require(conditional_potential(weights, groups, z, threshold - 1) >= 1,
                'least_certified_threshold')
    for length in range(graph.right_vertices + 1):
        prefix = tuple((index * 2 + 1) % groups for index in range(length))
        partial = prefix + (None,) * (graph.right_vertices - length)
        exact = conditional_potential(weights, groups, z, threshold, partial)
        enumerated = exhaustive_potential(weights, groups, z, threshold, prefix)
        require(exact == enumerated, 'conditional_formula_vs_exhaustive')
    result = derandomize_columns(weights, groups, z, threshold)
    for step in result.steps:
        require(sum(step.candidates, Fraction(0)) / groups == step.before, 'one_step_averaging')
        require(step.after <= step.before, 'monotonic_potential')
        require(step.after == min(step.candidates), 'minimum_candidate_chosen')
        if step.after < step.before:
            COUNTS['strict_potential_decreases'] += 1
    require(result.final_potential <= initial < 1, 'strict_final_certificate')
    require(result.maximum_load < threshold, 'integer_maxload_certificate')
    independently = exhaustive_potential(weights, groups, z, threshold, result.column_labels)
    require(result.final_potential == independently, 'final_potential_vs_cell_loads')
    require(sum(map(sum, result.cell_loads)) == graph.size, 'cell_mass_conservation')
    repeated = derandomize_columns(weights, groups, z, threshold)
    require(result == repeated, 'deterministic_column_labels')
    COUNTS['graph_parameter_cases'] += 1
    return result, row_labels


def check_packets(name, graph, alphabet, coordinates):
    groups = alphabet ** coordinates
    row_labels, _ = greedy_row_labels(graph, groups)
    weights = row_group_weights(graph, row_labels, groups)
    z = Fraction(3, 2)
    threshold = certified_threshold(weights, groups, z)
    result = derandomize_columns(weights, groups, z, threshold)
    embedding = make_packets(graph, row_labels, result.column_labels, alphabet, coordinates)
    length = 2 ** coordinates
    padded = embedding.padded_class_size
    require(padded % length == 0, 'packet_padding_integrality')
    require(len(embedding.packets) * length == padded * groups * groups, 'packet_count_identity')
    require(result.maximum_load <= padded < result.maximum_load + length,
            'packet_rounding_bound')
    seen = []
    padded_row = [[0] * alphabet for _ in range(coordinates)]
    padded_column = [[0] * alphabet for _ in range(coordinates)]
    real_row = [[0] * alphabet for _ in range(coordinates)]
    real_column = [[0] * alphabet for _ in range(coordinates)]
    for packet in embedding.packets:
        require(len(packet.slots) == length, 'packet_length')
        for position, edge_id in enumerate(packet.slots):
            expected_row = tuple(hi if (position >> coordinate) & 1 else lo
                                 for coordinate, (lo, hi) in enumerate(packet.symbol_pairs))
            expected_column = tuple(lo if (position >> coordinate) & 1 else hi
                                    for coordinate, (lo, hi) in enumerate(packet.symbol_pairs))
            for coordinate in range(coordinates):
                padded_row[coordinate][expected_row[coordinate]] += 1
                padded_column[coordinate][expected_column[coordinate]] += 1
            if edge_id is None:
                continue
            seen.append(edge_id)
            left, right = graph.edges[edge_id]
            actual_row = label_digits(row_labels[left], alphabet, coordinates)
            actual_column = label_digits(result.column_labels[right], alphabet, coordinates)
            require(actual_row == expected_row and actual_column == expected_column,
                    'packet_orientation_identity')
            for coordinate in range(coordinates):
                real_row[coordinate][actual_row[coordinate]] += 1
                real_column[coordinate][actual_column[coordinate]] += 1
    require(sorted(seen) == list(range(graph.size)), 'each_real_edge_embedded_once')
    marginal = padded * groups * groups // alphabet
    require(all(value == marginal for rows in (padded_row, padded_column) for row in rows for value in row),
            'exact_padded_symbol_marginals')
    require(all(value <= marginal for rows in (real_row, real_column) for row in rows for value in row),
            'real_symbol_port_bounds')
    COUNTS['packet_embedding_cases'] += 1


def negative_controls():
    calls = [lambda: Graph(1, 1, ((1, 0),)),
             lambda: Graph(1, 1, ((0, 1),)),
             lambda: greedy_row_labels(Graph(0, 0, ()), 0),
             lambda: conditional_potential(((1,),), 1, Fraction(1), 1),
             lambda: conditional_potential(((1,),), 1, Fraction(2), -1),
             lambda: conditional_potential(((1,),), 1, Fraction(2), 1, (2,)),
             lambda: row_group_weights(Graph(1, 1, ((0, 0),)), (2,), 2),
             lambda: make_packets(Graph(0, 0, ()), (), (), 2, 0)]
    for call in calls:
        try:
            call()
        except ValueError:
            COUNTS['negative_controls_rejected'] += 1
        else:
            raise RuntimeError('An invalid input was accepted')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, default=ROOT / 'results' / 'packing_checks.json')
    args = parser.parse_args()
    started = time.monotonic()
    cases = graph_cases()
    for name, graph in cases:
        for groups in (1, 2, 3):
            for z in (Fraction(3, 2), Fraction(5, 4)):
                check_graph(name, graph, groups, z)
    for name, graph in cases[:16]:
        for alphabet, coordinates in ((2, 1), (2, 2), (3, 1)):
            check_packets(name, graph, alphabet, coordinates)
    negative_controls()
    z, threshold, gate = asymptotic_parameters(100, 3, 2, 4)
    require(z == Fraction(49, 48) and threshold == 38 and not gate,
            'asymptotic_parameter_formula')
    require(COUNTS['strict_potential_decreases'] > 0, 'nontrivial_derandomization_exercised')
    output = {
        'status': 'pass',
        'scope': 'Exact finite balanced-labeling and packet-embedding prototype; not a SAT solver or proof of asymptotic runtime.',
        'certificate': 'Tiny graphs use the least integer threshold with exact initial potential below one; no claim they meet the asymptotic sufficient size gate.',
        'arithmetic': 'Python standard-library Fraction; all essential checks survive python -O.',
        'seed': 20261026,
        'distinct_graphs': len(cases),
        'counts': dict(sorted(COUNTS.items())),
        'elapsed_seconds': round(time.monotonic() - started, 6),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
