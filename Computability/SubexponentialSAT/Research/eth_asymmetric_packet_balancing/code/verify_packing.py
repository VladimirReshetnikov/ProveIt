#!/usr/bin/env python3
"""Reproducible exact finite checks for asymmetric balancing and packet geometry.

No assertion statements are used; Python -O runs the same checks. These checks
are finite component verification, not a proof or benchmark of the full solver.
"""
from argparse import ArgumentParser
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import random

from balanced_packing import balance_pair_labels, construct_packets


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def independent_loads(adjacency, row_labels, column_labels, Q):
    loads = [[0] * Q for _ in range(Q)]
    for row, values in enumerate(adjacency):
        for col, value in enumerate(values):
            loads[row_labels[row]][column_labels[col]] += value
    return loads


def independent_potential(adjacency, row_labels, column_labels, Q, q):
    return sum((q ** value for row in independent_loads(
        adjacency, row_labels, column_labels, Q) for value in row), Fraction(0))


def verify_balancing(adjacency, Q, h=8, exhaustive_completion=False):
    result = balance_pair_labels(adjacency, Q, h, True)
    ncols = len(adjacency[0]) if adjacency else 0
    M = sum(map(sum, adjacency))
    R = max(map(sum, adjacency), default=0)
    C = max((sum(row[j] for row in adjacency) for j in range(ncols)), default=0)
    q = Fraction(h * max(1, C) + 1, h * max(1, C))
    require(result['maximum_row_degree'] == R, 'Incorrect row-degree bound')
    require(result['maximum_column_degree'] == C, 'Incorrect column-degree bound')
    require(Fraction(result['potential_base']) == q, 'Potential used the wrong side degree')
    loads = independent_loads(adjacency, result['row_labels'], result['column_labels'], Q)
    require(loads == result['pair_loads'], 'Pair loads fail independent reconstruction')
    expected_rows = [sum(sum(adjacency[i]) for i, label in enumerate(result['row_labels'])
                         if label == a) for a in range(Q)]
    require(expected_rows == result['row_loads'], 'Row loads fail reconstruction')
    require(all(Q * value <= M + Q * R for value in expected_rows), 'Greedy bound failed')
    final = independent_potential(adjacency, result['row_labels'], result['column_labels'], Q, q)
    require(final == Fraction(result['final_potential']), 'Final potential is incorrect')
    require(final <= Fraction(result['initial_expected_potential']), 'Final potential increased')
    require(result['checked_assignment_steps'] == ncols, 'Assignment step missing')
    for step in result['steps']:
        scores = list(map(Fraction, step['candidate_scores']))
        require(sum(scores, Fraction(0)) / Q == Fraction(step['before']), 'Averaging failed')
        require(scores[step['selected_label']] == min(scores), 'Nonminimum label selected')
        require(Fraction(step['after']) == scores[step['selected_label']], 'Wrong after value')
    if exhaustive_completion:
        prefix = []
        for step in result['steps']:
            scores = []
            remaining = ncols - len(prefix) - 1
            for label in range(Q):
                total = sum((independent_potential(adjacency, result['row_labels'],
                             prefix + [label] + list(tail), Q, q)
                             for tail in product(range(Q), repeat=remaining)), Fraction(0))
                scores.append(total / (Q ** remaining))
            require(scores == list(map(Fraction, step['candidate_scores'])),
                    'Conditional expectation fails independent exhaustive completions')
            prefix.append(step['selected_label'])
    return result


def digits(label, base, width):
    # Deliberately separate from the module's packet construction.
    return [(label // (base ** coordinate)) % base for coordinate in range(width)]


def verify_packet_geometry(adjacency, row_labels, col_labels, packing):
    r, a = packing['group_count'], packing['coordinates']
    Q, L = r ** a, 2 ** a
    H = packing['common_padded_load']
    P = H * Q * Q
    packets = packing['packets']
    require(H % L == 0, 'Common padded load is not a multiple of packet length')
    pair_loads = independent_loads(adjacency, row_labels, col_labels, Q)
    largest = max((value for row in pair_loads for value in row), default=0)
    require(H == ((largest + L - 1) // L) * L, 'Common padded load is not the correct rounding')
    require(len(packets) * L == P, 'Wrong number of packets')
    require(packing['padded_ports_per_side'] == P, 'Wrong padded port count')
    expected_edges = [(i, j, copy) for i, row in enumerate(adjacency)
                      for j, value in enumerate(row) for copy in range(value)]
    require(expected_edges == packing['real_edges'], 'Edge inventory is wrong')
    seen_rows, seen_columns = Counter(), Counter()
    pair_slots = Counter()
    row_groups = [[0] * r for _ in range(a)]
    col_groups = [[0] * r for _ in range(a)]
    real_row_groups = [[0] * r for _ in range(a)]
    real_col_groups = [[0] * r for _ in range(a)]
    equal_packets = [0] * a
    for packet in packets:
        require(all(len(packet[key]) == L for key in
                    ('row_slots', 'column_slots', 'row_slot_labels', 'column_slot_labels')),
                'A packet has incorrect slot count')
        pairs = packet['symbol_pairs']
        require(len(pairs) == a, 'Packet coordinate count is wrong')
        for i, pair in enumerate(pairs):
            require(len(pair) == 2 and 0 <= pair[0] <= pair[1] < r, 'Invalid symbol pair')
            if pair[0] == pair[1]:
                equal_packets[i] += 1
        for slot in range(L):
            row_label = packet['row_slot_labels'][slot]
            col_label = packet['column_slot_labels'][slot]
            require(0 <= row_label < Q and 0 <= col_label < Q, 'Invalid padded label')
            pair_slots[row_label, col_label] += 1
            rd, cd = digits(row_label, r, a), digits(col_label, r, a)
            row_port, col_port = packet['row_slots'][slot], packet['column_slots'][slot]
            require((row_port is None) == (col_port is None), 'Unmatched real/dummy slot')
            for i in range(a):
                low, high = pairs[i]
                require(sorted([rd[i], cd[i]]) == [low, high], 'Unordered symbol pair varies')
                if low != high:
                    require(rd[i] == (high if (slot >> i) & 1 else low),
                            'Row orientation disagrees with slot bit')
                    require(cd[i] == (low if (slot >> i) & 1 else high),
                            'Column orientation disagrees with slot bit')
                row_groups[i][rd[i]] += 1
                col_groups[i][cd[i]] += 1
            if row_port is not None:
                edge_id, row_vertex = row_port
                col_edge_id, col_vertex = col_port
                require(edge_id == col_edge_id, 'Edge endpoints occupy different shared slots')
                require(0 <= edge_id < len(expected_edges), 'Invalid edge ID')
                require(expected_edges[edge_id][:2] == (row_vertex, col_vertex), 'Wrong endpoints')
                require(row_labels[row_vertex] == row_label, 'Wrong real row label')
                require(col_labels[col_vertex] == col_label, 'Wrong real column label')
                seen_rows[edge_id] += 1
                seen_columns[edge_id] += 1
                for i in range(a):
                    real_row_groups[i][rd[i]] += 1
                    real_col_groups[i][cd[i]] += 1
    expected_seen = Counter(range(len(expected_edges)))
    require(seen_rows == expected_seen and seen_columns == expected_seen,
            'An edge was omitted or repeated')
    require(all(pair_slots[x, y] == H for x in range(Q) for y in range(Q)),
            'Pair-label padding is not uniform')
    for i in range(a):
        require(r * equal_packets[i] == len(packets), 'Wrong equal-coordinate packet fraction')
        for g in range(r):
            require(r * row_groups[i][g] == P and r * col_groups[i][g] == P,
                    'Padded coordinate-group load is not uniform')
            require(real_row_groups[i][g] <= row_groups[i][g] and
                    real_col_groups[i][g] <= col_groups[i][g], 'Real load exceeds padding')
            require(r * (real_row_groups[i][g] + real_col_groups[i][g]) <= 2 * P,
                    'Child wire bound failed')
    return {'packets': len(packets), 'slots_per_side': P, 'edges': len(expected_edges)}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'results' / 'packing_checks.json')
    args = parser.parse_args()
    counts = {'original_exhaustive_cases': 0, 'original_random_cases': 0,
              'asymmetric_fixtures': 0, 'packet_geometry_cases': 0,
              'checked_padded_slots_per_side': 0, 'checked_packet_real_edges': 0,
              'negative_controls': 0, 'input_rejection_controls': 0}
    for values in product(range(4), repeat=4):
        adj = [list(values[:2]), list(values[2:])]
        for Q in (1, 2, 3, 4):
            verify_balancing(adj, Q, 4, exhaustive_completion=True)
            counts['original_exhaustive_cases'] += 1
    rng = random.Random(20261026)
    for _ in range(120):
        nr, nc, Q = rng.randrange(1, 9), rng.randrange(1, 9), rng.randrange(1, 6)
        adj = [[rng.randrange(6) if rng.random() < 0.5 else 0 for _ in range(nc)]
               for _ in range(nr)]
        verify_balancing(adj, Q, rng.randrange(2, 10))
        counts['original_random_cases'] += 1
    fixtures = [
        [[1] * 32], [[1] for _ in range(32)],
        [[3] * 17], [[3] for _ in range(17)],
        [[2 if j % 7 == i else 0 for j in range(70)] for i in range(7)],
        [[1 if (i + j) % 5 == 0 else 0 for j in range(5)] for i in range(55)],
        [], [[], []], [[0, 0], [0, 0]],
    ]
    asymmetry_observed = False
    for adj in fixtures:
        result = verify_balancing(adj, 4, 8)
        asymmetry_observed |= result['maximum_row_degree'] > result['maximum_column_degree']
        counts['asymmetric_fixtures'] += 1
    require(asymmetry_observed, 'Asymmetric fixture set failed to exercise unequal degrees')

    packet_fixtures = [[], [[], []], [[0]], [[7]], [[0, 3], [2, 1]],
                       [[1] * 9], [[2] for _ in range(9)],
                       [[2, 0, 1], [1, 3, 0], [0, 1, 2]]]
    saved = None
    for r, a in ((2, 0), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (4, 1)):
        Q = r ** a
        for adj in packet_fixtures:
            result = verify_balancing(adj, Q, 4)
            packing = construct_packets(adj, result['row_labels'], result['column_labels'], r, a)
            stats = verify_packet_geometry(adj, result['row_labels'], result['column_labels'], packing)
            counts['packet_geometry_cases'] += 1
            counts['checked_padded_slots_per_side'] += stats['slots_per_side']
            counts['checked_packet_real_edges'] += stats['edges']
            if r == 2 and a == 2 and adj == [[0, 3], [2, 1]]:
                saved = (adj, result, packing)
    require(saved is not None, 'Missing negative-control fixture')
    adj, labels, baseline = saved
    damaged = deepcopy(baseline)
    for packet in damaged['packets']:
        real = next((i for i, port in enumerate(packet['row_slots']) if port is not None), None)
        if real is not None:
            edge, vertex = packet['column_slots'][real]
            packet['column_slots'][real] = (edge + 1000, vertex)
            break
    for damage in (damaged, deepcopy(baseline)):
        if damage is not damaged:
            damage['packets'][0]['row_slot_labels'][0] ^= 1
        try:
            verify_packet_geometry(adj, labels['row_labels'], labels['column_labels'], damage)
        except RuntimeError:
            counts['negative_controls'] += 1
        else:
            raise RuntimeError('Invalid packet data was accepted')
    bad_calls = [lambda: balance_pair_labels([[1], [1, 2]], 2),
                 lambda: balance_pair_labels([[-1]], 2),
                 lambda: balance_pair_labels([[1]], 0),
                 lambda: balance_pair_labels([[1]], 2, 1),
                 lambda: construct_packets([[1]], [2], [0], 2, 1)]
    for call in bad_calls:
        try:
            call()
        except ValueError:
            counts['input_rejection_controls'] += 1
        else:
            raise RuntimeError('Invalid input was accepted')

    report = {
        'status': 'PASS', 'arithmetic': 'exact integers and fractions.Fraction',
        'original_balancing_cases_reproduced': counts['original_exhaustive_cases'] + counts['original_random_cases'],
        'counts': counts,
        'exhaustive_graphs': {'shape': [2, 2], 'multiplicities': [0, 1, 2, 3],
                             'label_counts': [1, 2, 3, 4]},
        'random_seed': 20261026,
        'verified': [
            'actual column degree determines potential base; row degree tracked separately',
            'exact conditional-expectation averaging and minimization at every column assignment',
            'independent exhaustive completion sums for all original 2x2 fixtures',
            'independent final pair loads and exact potential certificate',
            'uniform common pair load rounded upward to a multiple of packet length',
            'every real edge occurs once at identical row and column slots',
            'coordinate unordered pairs are fixed and unequal-pair orientation follows the slot bit',
            'packet count equals total padded ports divided by packet length',
            'equal-coordinate packet fraction is exactly 1/r',
            'each coordinate group has exactly total padded ports/r per side',
            'real coordinate-group loads and child wire counts respect padded bounds',
            'corrupted packet data and invalid inputs are rejected',
        ],
        'scope': 'Finite checks of new packing components only; no complete SAT solver, asymptotic empirical proof, or performance benchmark.',
        'checks_disabled_by_python_optimization': False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
