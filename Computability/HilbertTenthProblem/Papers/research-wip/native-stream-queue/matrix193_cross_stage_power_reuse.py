#!/usr/bin/env python3
"""Fresh exact power/repunit rescheduling; frozen programs are inert inputs only."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

PINS = {
    'matrix193_grouped_power_composition.py': '3facf356824eb762575e1b90bc2ad24812187f675e02406041408686a58b8a7e',
    'matrix193_grouped_power_composition.json': '67ec3453bb211f3129f27d4194084007c0e1e74410745a11c4181c79ae707002',
    'matrix193_grouped_power_composition.md': '66b145ba5d2c87ff3ca5cadee3a1f27de626d11315809ec18a181a88815a0d14',
    'matrix193_entry_controller_charts.py': '7c1e55ca1396958f234c2caf6c117702c4d69537cefcad51089498cb1e58f2bf',
    'matrix193_entry_controller_charts.json': 'd5b4490017c9b4ad46d700d8999ad1f5dedde789dd19a3d5f7b5375a1468a571',
    'matrix193_entry_controller_charts.md': '27245d944d03b1d31ad79470dfd5625798834b7a47c1a03dee319f198214d122',
}
# target, old operands, new operands, exact exponent (None for a repunit).
EDITS = [
    ('r166', 'r165', 'r165', 'r142', 'r136', 14),
    ('r138', 'r137', 'r137', 'r142', 'r143', 18),
    ('r551', 'r550', 'r550', 'r139', 'r145', 84),
    ('r173', 'r172', 'r172', 'r135', 'cp282', 140),
    ('r897', 'r896', 'r896', 'r134', 'r173', 142),
    ('cp526', 'r138', 'r552', 'r139', 'cp317', 186),
    ('r191', 'r190', 'r190', 'r148', 'r187', 194),
    ('r793', 'r792', 'r792', 'r187', 'cp282', 234),
    ('r554', 'r553', 'r553', 'r200', 'r191', 338),
    ('r803', 'r802', 'r802', 'r134', 'r554', 340),
    ('r798', 'r797', 'r797', 'r135', 'r794', 472),
    ('r772', 'r770', 'r771', 'r185', 'r204', None),
    ('r777', 'r776', 'r153', 'r154', 'r204', None),
]
DELETED = ['r137', 'r165', 'r169', 'r170', 'r171', 'r172', 'r190',
           'r546', 'r547', 'r548', 'r549', 'r550', 'r552', 'r553',
           'r764', 'r765', 'r766', 'r767', 'r768', 'r769', 'r770', 'r771',
           'r776', 'r788', 'r789', 'r790', 'r791', 'r792', 'r795', 'r796',
           'r797', 'r801', 'r802', 'r896']


def require(test, message):
    if not test:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def read_json(path):
    def pairs(items):
        out = {}
        for key, value in items:
            require(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    def bad(value):
        raise ValueError('nonfinite JSON ' + value)
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_constant=bad)


def type_equal(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type_equal(a[k], b[k]) for k in a)
    if type(a) is list:
        return len(a) == len(b) and all(type_equal(x, y) for x, y in zip(a, b))
    return a == b


def plus(a, b, sign=1):
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, 0) + sign * coefficient
        if not out[exponent]:
            del out[exponent]
    return out


def times(a, b):
    out = {}
    for i, x in a.items():
        for j, y in b.items():
            out[i+j] = out.get(i+j, 0) + x*y
    return {e: c for e, c in out.items() if c}


def pure_polynomials(rows, scale):
    values = {scale: {1: 1}}
    for name, operation, left, right in rows:
        if name == scale or not all(type(v) is int or v in values for v in (left, right)):
            continue
        def value(v):
            return ({0: v} if v else {}) if type(v) is int else values[v]
        a, b = value(left), value(right)
        values[name] = times(a, b) if operation == '*' else plus(a, b, 1 if operation == '+' else -1)
    return values


def live_set(rows, output):
    by_name = {row[0]: row for row in rows}
    live, todo = set(), [output]
    while todo:
        name = todo.pop()
        if type(name) is str and name not in live:
            live.add(name)
            if name in by_name:
                todo.extend(by_name[name][2:])
    return live


def schedule(rows, output):
    """Backward prune; walk old order, advancing dependencies only when required."""
    live = live_set(rows, output)
    retained = [r for r in rows if r[0] in live]
    by_name = {r[0]: r for r in retained}
    done, active, result = set(), set(), []
    def visit(name):
        if name in done or name not in by_name:
            return
        require(name not in active, 'acyclic rescheduling')
        active.add(name)
        for dependency in by_name[name][2:]:
            if type(dependency) is str:
                visit(dependency)
        active.remove(name)
        done.add(name)
        result.append(by_name[name])
    for row in retained:
        visit(row[0])
    require(len(result) == len(retained), 'acyclic rescheduling')
    return result, live


def audit(packet):
    rows = packet['source']
    free = packet['free']
    known = set(free)
    require(len(known) == len(free), 'distinct supplied ports')
    degree = {n: 0 if n in packet['fixed_numerals'] else 1 for n in free}
    counts = Counter()
    for name, op, a, b in rows:
        require(type(name) is str and name not in known and op in ('+', '-', '*'), 'fresh binary instruction')
        require(all(type(v) is int or (type(v) is str and v in known) for v in (a, b)), 'paid topological operands')
        da, db = (degree[v] if type(v) is str else 0 for v in (a, b))
        degree[name] = da + db if op == '*' else max(da, db)
        known.add(name)
        counts[op] += 1
    require(live_set(rows, packet['output']) == known, 'all rows and all supplied ports live')
    require(set(packet['witnesses']) <= set(free), 'witness interface')
    return {'total': len(rows), 'M': counts['*'], 'A': counts['+'] + counts['-'],
            'positive_witnesses': len(packet['witnesses']), 'supplied_ports': len(free),
            'fixed_coefficient_ports': len(packet['fixed_numerals']),
            'integer_literals': len({v for r in rows for v in r[2:] if type(v) is int}),
            'syntactic_degree_upper': degree[packet['output']], 'all_rows_and_ports_live': True}


def formal_identity(parent, child, scale, local_polynomials):
    """Congruence induction with each proved cut bound to the actual paid scale."""
    table = {}
    def token(key):
        if key not in table:
            table[key] = len(table)
        return table[key]
    free = {n: token(('port', n)) for n in parent['free']}
    def interpret(rows):
        env = dict(free)
        for name, op, a, b in rows:
            aa, bb = (env[v] if type(v) is str else token(('integer', v)) for v in (a, b))
            if name in local_polynomials:
                env[name] = token(('proved_polynomial', env[scale], tuple(sorted(local_polynomials[name].items()))))
            else:
                env[name] = token(('binary', op, aa, bb))
        return env
    before, after = interpret(parent['source']), interpret(child['source'])
    require(before[scale] == after[scale], 'scale bound to unchanged complete input expression')
    for name in after:
        require(before[name] == after[name], 'whole-source retained-register identity: ' + name)
    require(before[parent['output']] == after[child['output']], 'whole final polynomial identity')
    return {'local_cut_polynomials': len(local_polynomials),
            'retained_paid_registers': len(child['source']),
            'actual_scale_expression_identical': True, 'all_retained_registers_identical': True,
            'output_identity': 'F_child = F_immediate_parent on identical supplied coordinates over every commutative ring'}


def evaluate(packet, values, prime):
    env = {n: v % prime for n, v in values.items()}
    for n, op, a, b in packet['source']:
        x = env[a] if type(a) is str else a
        y = env[b] if type(b) is str else b
        env[n] = (x*y if op == '*' else x+y if op == '+' else x-y) % prime
    return env


def transform(parent, mapping, index, native_names, protected_names):
    def wire(name):
        return mapping.get(name, name) if type(name) is str else name
    old_rows = parent['source']
    old_by = {r[0]: r for r in old_rows}
    scale = wire('r108')
    old_poly = pure_polynomials(old_rows, scale)
    edits, cuts, certificates = {}, {}, []
    for name, old_a, old_b, a, b, exponent in EDITS:
        n, x, y = wire(name), wire(a), wire(b)
        old = [n, '*', wire(old_a), wire(old_b)]
        new = [n, '*', x, y]
        require(old_by[n] == old, 'literal mapped old producer')
        expected = {exponent: 1} if exponent is not None else {e: 1 for e in range(98 if name == 'r772' else 16)}
        require(old_poly[n] == expected == times(old_poly[x], old_poly[y]), 'exact old/new cut expansion')
        edits[n], cuts[n] = new, expected
        certificates.append({'original_names': [name, a, b], 'actual_names': [n, x, y],
                             'old_row': old, 'new_row': new,
                             'target_polynomial': [list(term) for term in sorted(expected.items())],
                             'left_polynomial': [list(term) for term in sorted(old_poly[x].items())],
                             'right_polynomial': [list(term) for term in sorted(old_poly[y].items())]})
    provisional = [edits.get(r[0], r[:]) for r in old_rows]
    rows, live = schedule(provisional, parent['output'])
    removed = [r for r in old_rows if r[0] not in live]
    require({r[0] for r in removed} == {wire(n) for n in DELETED}, 'exact34 dead definitions')
    require(Counter(r[1] for r in removed) == Counter({'*': 30, '+': 4}), '30M4A deletion')
    child = {k: parent[k] for k in ('variant', 'free', 'witnesses', 'fixed_numerals', 'fixture_fixed_bindings', 'output')}
    child['source'] = rows
    new_by = {r[0]: r for r in rows}
    for n, row in new_by.items():
        require(row == edits.get(n, old_by[n]), 'all retained non-edit definitions literal')
    new_poly = pure_polynomials(rows, scale)
    for n in new_poly:
        require(old_poly[n] == new_poly[n], 'every retained pure-scale polynomial')
    require(all(new_poly[n] == cuts[n] for n in cuts), 'all13 emitted cut identities')
    # Only scale-pure producers may cross a retained non-pure producer.
    old_nonpure = [r[0] for r in old_rows if r[0] in new_by and r[0] not in old_poly]
    new_nonpure = [r[0] for r in rows if r[0] not in old_poly]
    require(old_nonpure == new_nonpure, 'non-pure chronology retained')
    new_positions = {r[0]: j for j, r in enumerate(rows)}
    old_retained_positions = {r[0]: j for j, r in enumerate(r for r in old_rows if r[0] in new_by)}
    reordered = [n for n in new_by if new_positions[n] != old_retained_positions[n]]
    # Entire coefficient words, not just the changed monomial.
    coefficient_certificates = []
    for cert in parent['coefficient_certificates']:
        name = cert['wire']
        expected = {i: c for i, c in enumerate(cert['ascending_coefficients']) if c}
        require(old_poly[name] == new_poly[name] == expected, 'entire coefficient word expansion')
        coefficient_certificates.append({'wire': name, 'degree': max(expected),
                                         'ascending_coefficients': cert['ascending_coefficients'],
                                         'polynomial_sha256': digest(canonical(sorted(expected.items())))})
    component_names = {r[0] for r in parent['coefficient_component']}
    require(component_names <= set(new_by), 'no coefficient definition removed')
    component = [r for r in rows if r[0] in component_names]
    require({n for n in component_names if old_by[n] != new_by[n]} == {wire('cp526')}, 'single coefficient definition rewrite')
    component_counts = Counter(r[1] for r in component)
    require((len(component), component_counts['*'], component_counts['+']+component_counts['-']) == (553, 305, 248), '553 component ledger')
    child['coefficient_component'] = component
    child['component_ledger'] = {'total': 553, 'M': 305, 'A': 248}
    child['coefficient_certificates'] = coefficient_certificates
    # Full retained native, residual, finalizer and previously paid population work.
    for name in native_names + protected_names:
        require(new_by[wire(name)] == old_by[wire(name)], 'protected literal row ' + name)
    residuals = parent['retained_residual_wires']
    require(all(new_by[n] == old_by[n] for n in residuals), 'all residual producers literal')
    finalizer_count = 3*len(residuals)+2
    require(rows[-finalizer_count:] == old_rows[-finalizer_count:], 'complete finalizer literal')
    child['retained_residual_wires'] = residuals
    before_ledger, ledger = audit(parent), audit(child)
    require((ledger['total'], ledger['M'], ledger['A']) == (before_ledger['total']-34, before_ledger['M']-30, before_ledger['A']-4), 'fresh full-source saving')
    ledger.update(exact_degree=parent['ledger']['exact_degree'], outer_residuals=len(residuals))
    child['ledger'] = ledger
    child['local_identities'] = certificates
    child['removed_rows'] = removed
    child['whole_identity'] = formal_identity(parent, child, scale, cuts)
    child['rescheduling'] = {'rule': 'backward liveness, then original-order traversal emitting not-yet-emitted dependencies first',
                             'nonpure_relative_order_unchanged': True,
                             'retained_position_changes': reordered,
                             'all_operands_paid_in_emitted_order': True}
    child['literal_boundary'] = {'native_rows': len(native_names), 'group_and_population_rows': len(protected_names),
                                'residual_producers': len(residuals), 'finalizer_rows': finalizer_count,
                                'other_retained_definitions': len(rows)-len(edits)}
    child['parent_reference'] = {'receipt': 'matrix193_grouped_power_composition.json', 'packet_index': index,
                                 'source_array_sha256': digest(canonical(old_rows)), 'fresh_ledger': before_ledger}
    child['degree_transfer'] = {'exact_degree': ledger['exact_degree'],
                               'reason': 'full polynomial identity on identical variables; inherited valid-program specialization theorem',
                               'new_degree_certificate_claimed': False}
    rng = random.Random(1534+index)
    tests = []
    for prime in (1000000007, 1000000009):
        for case in range(4):
            values = {n: rng.randrange(-101, 102) for n in child['free']}
            if case % 2 == 0:
                values.update(child['fixture_fixed_bindings'])
            old_values = evaluate(parent, values, prime)
            new_values = evaluate(child, values, prime)
            require(all(old_values[n] == v for n, v in new_values.items()), 'supplemental entire register comparison')
            tests.append({'prime': prime, 'case': case, 'illustrative_fixed_bindings': case % 2 == 0,
                          'output': new_values[child['output']]})
    child['supplemental_modular_checks'] = tests
    return child


def build(root, parent_root):
    for name, expected in PINS.items():
        directory = parent_root if name.startswith('matrix193_grouped_power_composition.') else root
        require(digest((directory/name).read_bytes()) == expected, 'frozen byte pin: ' + name)
    parent = read_json(parent_root/'matrix193_grouped_power_composition.json')
    charts = read_json(root/'matrix193_entry_controller_charts.json')
    require(parent['source_sha256'] == PINS['matrix193_grouped_power_composition.py'], 'parent source binding')
    require(charts['source_sha256'] == PINS['matrix193_entry_controller_charts.py'], 'chart source binding')
    require(len(parent['packets']) == 4 and len(charts['packets']) == 3, 'full packet inventory')
    baseline = parent['packets'][0]['source']
    names = [r[0] for r in baseline]
    native = names[names.index('selection__bs_even'):names.index('eight_units')+1]
    require(len(native) == 63, 'native cut inventory')
    # These are already-paid, unchanged predecessors of the complete source.
    protected = ['r'+str(i) for i in range(110, 134)]
    protected += [r[0] for r in baseline if r[0].startswith('grouped_population_sum_')]
    protected += ['r103']
    require(len(protected) == 97, '24 groups and73 population producers')
    packets = [transform(p, {} if i == 0 else charts['packets'][i-1]['map'], i, native, protected)
               for i, p in enumerate(parent['packets'])]
    require([p['ledger']['total'] for p in packets] == [1534, 1531, 1531, 1528], 'complete final totals')
    require([p['ledger']['positive_witnesses'] for p in packets] == [145, 144, 144, 143], 'witness counts')
    return {'schema': 'matrix193-cross-stage-power-reuse-v1',
            'source_sha256': digest(Path(__file__).read_bytes()), 'pins': PINS, 'packets': packets,
            'fresh_evidence': {'complete_arrays': 4, 'complete_rows': sum(len(p['source']) for p in packets),
                               'local_polynomial_identities': 52, 'full_coefficient_words': 16,
                               'coefficient_entries': sum(len(c['ascending_coefficients']) for p in packets for c in p['coefficient_certificates']),
                               'whole_source_identities': 4, 'signed_modular_register_maps': 32},
            'scope': {'frozen_code_executed_or_imported': False, 'identical_supplied_coordinates': True,
                      'all_ring_identity_to_immediate_parent': True, 'same_positive_integer_zero_tuples': True,
                      'pre_IDLE_comparison': 'ordinary input projection only', 'valid_fixed_program_recipe_unchanged': True,
                      'exact_degrees_inherited': True, 'new_native_Pell_or_accepting_fixture': False,
                      'universal84_unchanged': True, 'minimality_claim': False}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--parent-root', type=Path)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--output', type=Path)
    group.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = build(args.root, args.parent_root or args.root)
    if args.output:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    else:
        require(type_equal(result, read_json(args.expect)), 'type-exact complete receipt')
    print('PASS: complete1534/1531/1531/1528; 30M4A saved each; all-ring identities; unchanged interfaces/degrees')


if __name__ == '__main__':
    main()
