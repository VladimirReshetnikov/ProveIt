#!/usr/bin/env python3
"""Bounded matrix193 lookup schedule scout; imports no predecessor code."""
import argparse
import hashlib
import itertools
import json
import math
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

PINS = {
    'matrix193_synchronized_rows.py': 'da55246efc8047b6b3f188579cf6c71bbabb067def3fe04ac47ba61b56517e52',
    'matrix193_synchronized_rows.json': '9ce8537fc12bff3a2d3d91297d65a47ee6a7af193ff4bb08f474216260ef4233',
    'matrix193_synchronized_rows.md': 'ab768aa392841add5dc6dfcd8ed62564ca17fae2fe80e5ec39f1f4ceb36559d2',
}
COLUMNS = ['K0', 'K1', 'K2', 'K3', 'G0', 'G1', 'G2', 'G3']
D = math.factorial(95)


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    out = {}
    for k, v in pairs:
        require(k not in out, 'duplicate JSON key: ' + k)
        out[k] = v
    return out


def bad_constant(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def read_json(raw):
    return json.loads(raw, object_pairs_hook=unique_object, parse_constant=bad_constant)


def exact_equal(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact_equal(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact_equal(x, y) for x, y in zip(a, b))
    return a == b


def consecutive_coefficients(rows):
    out = []
    for col in range(8):
        values = [r[col] for r in rows]
        coefficients = []
        for j in range(96):
            coefficients.append(values[0] * (D // math.factorial(j)))
            values = [b - a for a, b in zip(values, values[1:])]
        out.append(coefficients)
    return out


def coefficient_summary(coefficients):
    zeros = [[col, j] for col in range(8) for j in range(1, 96)
             if coefficients[col][j] == 0]
    return {
        'zero_nonconstant_coefficients': zeros,
        'nonconstant_terms': 760 - len(zeros),
        'maximum_coefficient_magnitude_bits': max(abs(c).bit_length() for col in coefficients for c in col),
        'within_layer_equal_or_opposite_nonzero_pairs': [
            [j, a, b] for j in range(1, 96) for a in range(8) for b in range(a + 1, 8)
            if coefficients[a][j] and abs(coefficients[a][j]) == abs(coefficients[b][j])],
    }


def rank_certificate(rows, ids):
    basis = []
    selected = []
    for index, row in enumerate(rows):
        v = [Fraction(x) for x in [1] + row]
        for pivot, base in basis:
            c = v[pivot]
            v = [a - c * b for a, b in zip(v, base)]
        pivot = next((j for j, x in enumerate(v) if x), None)
        if pivot is not None:
            c = v[pivot]
            basis.append((pivot, [x / c for x in v]))
            selected.append(index)
        if len(basis) == 9:
            break
    require(len(basis) == 9, 'unexpected affine dependence')
    matrix = [[Fraction(x) for x in [1] + rows[i]] for i in selected]
    determinant = Fraction(1)
    for k in range(9):
        pivot = next(i for i in range(k, 9) if matrix[i][k])
        if pivot != k:
            matrix[k], matrix[pivot] = matrix[pivot], matrix[k]
            determinant = -determinant
        v = matrix[k][k]
        determinant *= v
        for i in range(k + 1, 9):
            c = matrix[i][k] / v
            matrix[i] = [x - c * y for x, y in zip(matrix[i], matrix[k])]
    require(determinant.denominator == 1 and determinant != 0, 'rank determinant')
    return {'augmented_rank': 9, 'selected_row_indices': selected,
            'selected_tile_ids': [ids[i] for i in selected],
            'minor': [[1] + rows[i] for i in selected], 'minor_determinant': int(determinant)}


def emit_lookup(coefficients, tile_ids):
    instructions = []
    def gate(name, op, left, right):
        instructions.append([name, op, left, right])
        return name
    shifts = ['z'] + [gate('z_minus_' + str(k), '-', 'z', k) for k in range(1, 96)]
    prefixes = [1, 'z']
    for j in range(2, 97):
        prefixes.append(gate('falling_' + str(j), '*', prefixes[-1], shifts[j - 1]))
    outputs = []
    for col, cc in enumerate(coefficients):
        value = cc[0]
        require(value != 0, 'constant term schedule premise')
        for j in range(1, 96):
            c = cc[j]
            if not c:
                continue
            require(abs(c) != 1, 'unit coefficient schedule premise')
            term = gate('term_' + str(col) + '_' + str(j), '*', c, prefixes[j])
            value = gate('sum_' + str(col) + '_' + str(j), '+', value, term)
        outputs.append(value)
    known = {'z'}
    for name, op, left, right in instructions:
        require(name not in known and op in ['+', '-', '*'], 'invalid row')
        require(all(type(v) is int or type(v) is str and v in known for v in [left, right]), 'forward reference')
        known.add(name)
    live = set(outputs + [prefixes[96]])
    for name, op, left, right in reversed(instructions):
        if name in live:
            live.update(v for v in [left, right] if isinstance(v, str))
    require(all(row[0] in live for row in instructions) and 'z' in live, 'dead lookup row')
    m = sum(row[1] == '*' for row in instructions)
    return {'input': 'z', 'selector_tile_order': tile_ids, 'scale': D,
            'coefficients': coefficients, 'instructions': instructions,
            'selector_polynomial_output': prefixes[96], 'column_outputs': outputs,
            'ledger': {'M': m, 'A': len(instructions) - m, 'total': len(instructions)},
            'all_rows_live': True}


def evaluate_lookup(packet, z):
    values = {'z': z}
    def value(v):
        return v if type(v) is int else values[v]
    for name, op, left, right in packet['instructions']:
        a, b = value(left), value(right)
        values[name] = a * b if op == '*' else a + b if op == '+' else a - b
    return values[packet['selector_polynomial_output']], [values[v] for v in packet['column_outputs']]


def irregular_summary(rows):
    first = rows[0][4]
    stride = math.gcd(*(r[4] - first for r in rows))
    nodes = [(r[4] - first) // stride for r in rows]
    require(stride == 5 and nodes[0] == 0 and len(set(nodes)) == 96, 'irregular nodes')
    denominators = [math.prod(nodes[i] - nodes[j] for j in range(96) if j != i) for i in range(96)]
    scale = math.lcm(*denominators)
    coefficients = []
    for col in range(8):
        values = [r[col] * scale for r in rows]
        cc = [values[0]]
        for k in range(1, 96):
            next_values = []
            for i in range(len(values) - 1):
                quotient, remainder = divmod(values[i + 1] - values[i], nodes[i + k] - nodes[i])
                require(remainder == 0, 'uncleared divided difference')
                next_values.append(quotient)
            values = next_values
            cc.append(values[0])
        coefficients.append(cc)
    require(coefficients[4] == [scale * first, scale * stride] + [0] * 94, 'affine selected column')
    require(all(abs(c) != 1 for cc in coefficients for c in cc if c), 'unit coefficient irregular premise')
    # Exact Newton interpolation at all 96 nodes, without emitting a large source array.
    for i, z in enumerate(nodes):
        for col, cc in enumerate(coefficients):
            value = cc[-1]
            for j in range(94, -1, -1):
                value = value * (z - nodes[j]) + cc[j]
            require(value == scale * rows[i][col], 'irregular interpolation')
    summary = coefficient_summary(coefficients)
    require(summary['zero_nonconstant_coefficients'] == [[4, j] for j in range(2, 96)], 'irregular zero set')
    ordered = sorted(nodes)
    negative_z = next(ordered[i] + 1 for i in range(0, 95, 2) if ordered[i + 1] - ordered[i] > 1)
    selector_value = math.prod(negative_z - v for v in nodes)
    require(selector_value < 0, 'irregular integer nonnegativity counterexample')
    # Measure a declared coefficient-only JSON representation, but never save it.
    payload = {'nodes': nodes, 'scale_hex': hex(scale),
               'coefficients_hex': [[hex(v) for v in cc] for cc in coefficients],
               'selected_column': 4, 'affine_selector_column': {'constant': first, 'coefficient': stride}}
    serialized = (json.dumps(payload, indent=2) + '\n').encode()
    return {'nodes': nodes, 'column': 'G0', 'node_shift': first, 'node_stride': stride,
            'maximum_node_magnitude_bits': max(abs(x).bit_length() for x in nodes),
            'common_scale_bits': scale.bit_length(), 'common_scale_hex_sha256': sha(hex(scale).encode()),
            'coefficient_only_json_bytes': len(serialized), 'coefficient_only_json_sha256': sha(serialized),
            'coefficient_summary': summary, 'proposed_lookup_ledger': {'M': 761, 'A': 761, 'total': 1522},
            'all_768_interpolation_values_checked': True,
            'integer_selector_negative_example': {'z': negative_z, 'sign': -1},
            'large_coefficients_or_source_emitted': False, 'full_predicate_emitted': False}


def verify(root):
    for name, expected in PINS.items():
        require(sha((root / name).read_bytes()) == expected, 'pin mismatch: ' + name)
    parent = read_json((root / 'matrix193_synchronized_rows.json').read_bytes())
    require(parent['source_sha256'] == PINS['matrix193_synchronized_rows.py'], 'parent self pin')
    table = parent['transition_table']
    require(type(table) is list and len(table) == 96, 'transition count')
    require(all(type(r) is dict and set(r) == {'tile_id', 'G', 'H', 'K'} for r in table), 'table schema')
    require(all(type(r['tile_id']) is int and all(type(r[k]) is list and len(r[k]) == 4
                and all(type(x) is int for x in r[k]) for k in ['G', 'H', 'K']) for r in table), 'table types')
    ids = [r['tile_id'] for r in table]
    require(len(set(ids)) == 96, 'tile IDs')
    rows = [r['K'] + r['G'] for r in table]
    require(all(r[k][0] * r[k][3] - r[k][1] * r[k][2] == 1 for r in table for k in ['G', 'H', 'K']), 'determinants')
    groups = defaultdict(list)
    for i, r in enumerate(rows):
        groups[tuple(r[:4])].append(i)
    prefix_trials = []
    for group in groups.values():
        if len(group) < 2:
            continue
        for prefix in itertools.permutations(group):
            order = list(prefix) + [i for i in range(96) if i not in group]
            cc = consecutive_coefficients([rows[i] for i in order])
            stats = coefficient_summary(cc)
            prefix_trials.append({'prefix_tile_ids': [ids[i] for i in prefix],
                                  'zero_nonconstant_coefficients': stats['zero_nonconstant_coefficients'],
                                  'maximum_coefficient_magnitude_bits': stats['maximum_coefficient_magnitude_bits']})
    require(len(prefix_trials) == 78, 'finite permutation grammar count')
    require(max(len(r['zero_nonconstant_coefficients']) for r in prefix_trials) == 12, 'prefix result')
    extra_orders = [('literal', list(range(96))), ('reverse', list(reversed(range(96))))]
    extra_orders += [('sort_' + COLUMNS[j], sorted(range(96), key=lambda i: rows[i][j])) for j in range(8)]
    extra_trials = [{'name': name, 'tile_order': [ids[i] for i in order],
                     'statistics': coefficient_summary(consecutive_coefficients([rows[i] for i in order]))}
                    for name, order in extra_orders]
    prefix = [ids.index(i) for i in [109, 110, 111, 112]]
    cleanup_order = prefix + [i for i in range(96) if i not in prefix]
    packets = []
    for name, order in [('literal', list(range(96))), ('cleanup_ascending', cleanup_order)]:
        cc = consecutive_coefficients([rows[i] for i in order])
        packet = emit_lookup(cc, [ids[i] for i in order])
        for j, i in enumerate(order):
            selector, values = evaluate_lookup(packet, j)
            require(selector == 0 and values == [D * v for v in rows[i]], 'literal source interpolation')
        packet['name'] = name
        packet['statistics'] = coefficient_summary(cc)
        packets.append(packet)
    require(packets[0]['ledger'] == {'M': 855, 'A': 855, 'total': 1710}, 'literal ledger')
    require(packets[1]['ledger'] == {'M': 843, 'A': 843, 'total': 1686}, 'cleanup ledger')
    require(packets[1]['statistics']['zero_nonconstant_coefficients'] == [[c, j] for c in range(4) for j in range(1, 4)], 'cleanup zeros')
    return {'status': 'PASS', 'scope': 'Bounded 96-row lookup schedules, not an unbounded product certificate or universal operation bound.',
            'source_sha256': sha(Path(__file__).read_bytes()), 'pins': dict(PINS), 'predecessor_code_executed': False,
            'columns': COLUMNS, 'table_rows': 96, 'scale_bits': D.bit_length(),
            'distinct_entries_per_column': [len({r[j] for r in rows}) for j in range(8)],
            'distinct_K_matrices': len(groups), 'distinct_G_matrices': len({tuple(r[4:]) for r in rows}),
            'K_multiplicity_histogram': {str(k): v for k, v in sorted(Counter(map(len, groups.values())).items())},
            'affine_rank_certificate': rank_certificate(rows, ids),
            'repeated_K_prefix_trials': prefix_trials, 'additional_orders': extra_trials,
            'lookup_packets': packets, 'irregular_nodes': irregular_summary(rows),
            'nested_Newton_Horner_lookup_costs': {'literal': 1710, 'cleanup_ascending': 1698,
                                                'cleanup_with_shared_falling4_factor': 1686},
            'checks': {'prefix_permutations': 78, 'additional_orders': 10, 'emitted_lookup_rows': 3396,
                       'emitted_node_column_values': 1536, 'irregular_node_column_values': 768,
                       'full_unbounded_certificate_emitted': False, 'global_arithmetic_optimality_claimed': False}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True, help='Directory containing the pinned synchronized-row trio')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--expect', type=Path)
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    receipt = verify(args.root)
    if args.expect:
        require(exact_equal(receipt, read_json(args.expect.read_bytes())), 'receipt mismatch')
    else:
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print('PASS: 78 prefix permutations; 24-gate cleanup saving; 3396 live lookup rows; rank 9; irregular-node tradeoff scoped.')


if __name__ == '__main__':
    main()
