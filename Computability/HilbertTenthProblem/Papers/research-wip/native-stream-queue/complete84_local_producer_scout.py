#!/usr/bin/env python3
"""Pinned finite producer-rewrite obstruction for the unchanged complete84 source.

Finite-field evaluations only reject identities. All surviving replacement
schedules receive a complete output-liveness cost check. No old Python executes.
"""
import argparse
import hashlib
import json
import random
from pathlib import Path

PINS = {
    'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737',
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}
MODULI = (1000000007, 1000000009, 998244353)
SEED = 841037
CONSTANTS = tuple(range(5))
EXCLUDED_NAMES = {'all_units', 'seven_units', 'polynomial'}
TEMP = '__local_producer_scout_temporary'


def need(test, message):
    if not test:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def exact(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(exact(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact(a, b) for a, b in zip(left, right))
    return left == right


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def reject_constant(value):
    raise ValueError('nonfinite JSON number: ' + value)


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object,
                      parse_constant=reject_constant)


def operation(symbol, left, right):
    return tuple((a+b if symbol == '+' else a-b if symbol == '-' else a*b) % modulus
                 for a, b, modulus in zip(left, right, MODULI))


def live_source(rows, output):
    definitions = {name: (symbol, left, right) for name, symbol, left, right in rows}
    live, work = set(), [output]
    while work:
        name = work.pop()
        if name not in live:
            live.add(name)
            if name in definitions:
                work.extend(port for port in definitions[name][1:] if type(port) is str)
    return [row for row in rows if row[0] in live], live


def search(packet):
    rows, free, output = packet['source'], packet['free'], packet['output']
    need(type(rows) is list and len(rows) == 84, 'complete 84-row parent')
    need(type(free) is list and len(free) == 25 and len(set(free)) == 25,
         'complete distinct 25-port interface')
    need(all(type(name) is str for name in free), 'free port types')
    rng = random.Random(SEED)
    values = {name: tuple(rng.randrange(2, modulus-2) for modulus in MODULI) for name in free}
    for constant in CONSTANTS:
        values[constant] = tuple(constant % modulus for modulus in MODULI)
    known = set(free)
    multiplications = 0
    for row in rows:
        need(type(row) is list and len(row) == 4, 'binary gate record')
        name, symbol, left, right = row
        need(type(name) is str and name not in known and name != TEMP, 'fresh gate name')
        need(symbol in ('+', '-', '*'), 'legal operation')
        for port in (left, right):
            need(type(port) is int or type(port) is str and port in known, 'source closure')
            if type(port) is int and port not in values:
                values[port] = tuple(port % modulus for modulus in MODULI)
        values[name] = operation(symbol, values[left], values[right])
        known.add(name)
        multiplications += symbol == '*'
    retained, live = live_source(rows, output)
    need(retained == rows and live == known, 'all source gates and free ports are live')
    need(multiplications == 47 and len(packet['witnesses']) == 18, 'parent paid ledger')
    counts = {'targets': 0, 'pair_expressions': 0, 'one_operation_matches': 0,
              'two_operation_matches': 0, 'shared_temporary_matches': 0, 'zero_operation_alias_tests': 0,
              'zero_operation_alias_matches': 0, 'multiplication_zero_rejections': 0}
    per_target = []
    lower = []
    for index, (target, _, _, _) in enumerate(rows):
        if target.startswith('norm_') or target in EXCLUDED_NAMES:
            continue
        ports = free + list(CONSTANTS) + [row[0] for row in rows[:index]]
        goal = values[target]
        record = {'target': target, 'zero_operation_matches': 0,
                  'one_operation_matches': 0, 'two_operation_matches': 0,
                  'shared_temporary_matches': 0, 'minimum_surviving_cost': None}
        # An alias is an edge substitution, not a zero-cost arithmetic gate.
        for port in ports:
            counts['zero_operation_alias_tests'] += 1
            if values[port] != goal:
                continue
            counts['zero_operation_alias_matches'] += 1
            record['zero_operation_matches'] += 1
            revised = rows[:index] + [[name, symbol,
                                      port if left == target else left,
                                      port if right == target else right]
                                     for name, symbol, left, right in rows[index+1:]]
            pruned, _ = live_source(revised, output)
            cost = len(pruned)
            record['minimum_surviving_cost'] = cost if record['minimum_surviving_cost'] is None else min(cost, record['minimum_surviving_cost'])
            if cost < len(rows):
                lower.append({'target': target, 'alias': port, 'total': cost, 'source': pruned})
        # Keep every expression in an evaluation bucket; there is no hash-only
        # equality argument and no representative selection that can hide cost.
        pair = {}
        for i, left in enumerate(ports):
            for j, right in enumerate(ports):
                for symbol in ('+', '-', '*'):
                    if symbol != '-' and j < i:
                        continue
                    value = operation(symbol, values[left], values[right])
                    pair.setdefault(value, []).append((symbol, left, right))
                    counts['pair_expressions'] += 1
        schedules = [([target, *triple],) for triple in pair.get(goal, [])]
        record['one_operation_matches'] = len(schedules)
        for port in ports:
            value = values[port]
            requests = [('+', tuple((g-a) % m for g, a, m in zip(goal, value, MODULI)), True),
                        ('-', tuple((a-g) % m for g, a, m in zip(goal, value, MODULI)), True),
                        ('-', tuple((g+a) % m for g, a, m in zip(goal, value, MODULI)), False)]
            if all(value):
                requests.append(('*', tuple(g*pow(a, -1, m) % m for g, a, m in zip(goal, value, MODULI)), True))
            else:
                need(any(g != 0 for g, a in zip(goal, value) if a == 0),
                     'degenerate multiplication bucket requires explicit enumeration')
                counts['multiplication_zero_rejections'] += 1
            for outer, wanted, port_left in requests:
                for inner in pair.get(wanted, []):
                    final = [target, outer, port, TEMP] if port_left else [target, outer, TEMP, port]
                    schedules.append(([TEMP, *inner], final))
                    record['two_operation_matches'] += 1
        # A two-operation DAG can use its new temporary twice (e.g. a square).
        # This is separate from the two-operation tree shapes above.
        for value, expressions in pair.items():
            for outer in ('+', '-', '*'):
                if operation(outer, value, value) == goal:
                    for inner in expressions:
                        schedules.append(([TEMP, *inner], [target, outer, TEMP, TEMP]))
                        record['shared_temporary_matches'] += 1
                        record['two_operation_matches'] += 1
        counts['shared_temporary_matches'] += record['shared_temporary_matches']
        counts['targets'] += 1
        counts['one_operation_matches'] += record['one_operation_matches']
        counts['two_operation_matches'] += record['two_operation_matches']
        for replacement in schedules:
            revised = rows[:index] + list(replacement) + rows[index+1:]
            pruned, _ = live_source(revised, output)
            cost = len(pruned)
            record['minimum_surviving_cost'] = cost if record['minimum_surviving_cost'] is None else min(cost, record['minimum_surviving_cost'])
            if cost < len(rows):
                lower.append({'target': target, 'replacement': replacement, 'total': cost, 'source': pruned})
        per_target.append(record)
    need(not lower, 'a lower-cost fingerprint candidate requires exact symbolic review')
    return {'moduli': list(MODULI), 'seed': SEED, 'constants': list(CONSTANTS),
            'free_port_evaluations': {name: list(values[name]) for name in free},
            'counts': counts, 'per_target': per_target, 'lower_cost_candidates': lower,
            'parent_gate_liveness': len(retained), 'parent_free_liveness': len(free),
            'parent_paid_ledger': {'M': multiplications, 'A': len(rows)-multiplications, 'total': len(rows)}}


def verify(root):
    for name, digest in PINS.items():
        need(sha((root/name).read_bytes()) == digest, 'parent pin: ' + name)
    parent = read_json(root/'complete84_scaled_strong_output.json')
    need(parent['source_sha256'] == PINS['complete84_scaled_strong_output.py'], 'parent self-source pin')
    packet = parent['packet']
    result = search(packet)
    return {'status': 'PASS', 'source_sha256': sha(Path(__file__).read_bytes()),
            'parent_pins': dict(PINS), 'packet': packet, 'search': result,
            'grammar': {'targets': 'All source names except norm_* and all_units/seven_units/polynomial',
                        'leaves': 'Free ports, constants 0..4, and strictly earlier original registers',
                        'replacement_shapes': ['alias a', 'op(a,b)', 'op(a,op(b,c))', 'op(op(b,c),a)', 'op(v,v), v=op(a,b)'],
                        'operations': ['+', '-', '*'],
                        'cost': 'All binary operations live at the complete original polynomial output'},
            'conclusion': 'No all-value identity in this finite grammar lowers the complete paid total below 84.',
            'limitations': ['Not a global arithmetic lower bound', 'Not a positive-zero-only search',
                            'Does not exploit valid fixed-numeral recipe relations',
                            'Does not use later registers, multiple simultaneous rewrites, or new coordinates',
                            'Finite-field matches are not asserted to be exact identities',
                            'Exact degree is inherited with the unchanged source, not re-proved here'],
            'predecessor_Python_executed': False, 'new_universal_upper_bound_claim': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--expect', type=Path)
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(args.root.resolve())
    serialized = json.dumps(result, indent=2, sort_keys=True) + '\n'
    need(exact(result, json.loads(serialized)), 'type-exact JSON round trip')
    if args.expect:
        need(exact(result, read_json(args.expect)), 'type-exact expected receipt')
    else:
        args.output.write_text(serialized)
    print(json.dumps({'status': 'PASS', 'counts': result['search']['counts'],
                      'lower_cost_candidates': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
