#!/usr/bin/env python3
"""Independent, data-only audit of the emitted clean-clock arithmetic DAGs.

No project Python module is imported or executed. The only mathematical inputs
are JSON arithmetic DAGs. This checker and its results stay in the audit folder.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

PIN = 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e'
MOD = 1000003
NATIVE = {
    'incdec': (604, 239, 365, 60, 2344),
    'zero3': (479, 184, 295, 58, 1192),
    'nop': (477, 182, 295, 58, 1192),
    'positive3': (480, 189, 291, 58, 1192),
}


def need(condition, reason):
    if not condition:
        raise ValueError(reason)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Repeated JSON object key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def dag_shape(circuit):
    parameters, witnesses = circuit['parameters'], circuit['auxiliaries']
    need(type(parameters) is list and type(witnesses) is list, 'Port lists')
    ports = parameters + witnesses
    need(all(type(x) is str for x in ports), 'String ports')
    need(len(set(ports)) == len(ports), 'Disjoint distinct ports')
    declared, definitions, literals = set(ports), {}, set()
    mults = adds = 0
    for row in circuit['source']:
        need(type(row) is list and len(row) == 4, 'Four-field gate')
        name, operation, left, right = row
        need(type(name) is str and name not in declared, 'Unique fresh gate')
        need(operation in ('+', '-', '*'), 'Allowed arithmetic operation')
        for operand in (left, right):
            need(type(operand) is int or type(operand) is str and operand in declared,
                 'Earlier declared operand, with booleans forbidden')
            if type(operand) is int:
                literals.add(operand)
        definitions[name] = (operation, left, right)
        declared.add(name)
        mults += operation == '*'
        adds += operation != '*'
    need(circuit['output'] in definitions, 'Output is emitted gate')
    reached, stack = set(), [circuit['output']]
    while stack:
        atom = stack.pop()
        if type(atom) is not str or atom in reached:
            continue
        reached.add(atom)
        if atom in definitions:
            stack.extend(definitions[atom][1:])
    need(reached == declared, 'Every declared gate and coordinate is output-live')
    return {
        'total': len(definitions), 'M': mults, 'A': adds,
        'positive_witnesses': len(witnesses),
        'natural_parameters': len(parameters),
        'integer_literals': sorted(literals),
        'all_gates_live': True, 'all_coordinates_live': True,
    }


def sos_tail(circuit, prefix):
    """Check the full suffix as a formal sum of the listed residual squares."""
    pairs = circuit['comparisons']
    need(pairs and all(type(p) is list and len(p) == 2 for p in pairs), 'Pairs')
    n = len(pairs)
    gate_count = 3*n - 1
    suffix = circuit['source'][-gate_count:]
    need(len(suffix) == gate_count, 'Complete SOS suffix')
    residuals, squares = [], []
    for i, pair in enumerate(pairs):
        subtraction, square = suffix[2*i:2*i+2]
        need(subtraction[1:] == ['-', *pair], 'Every comparison subtracted exactly')
        need(square[1:] == ['*', subtraction[0], subtraction[0]], 'Every residual squared')
        need(subtraction[0] == prefix + '_res' + str(i), 'Residual label')
        need(square[0] == prefix + '_sq' + str(i), 'Square label')
        residuals.append(subtraction[0])
        squares.append(square[0])
    collected = {squares[0]: {squares[0]: 1}}
    for i, row in enumerate(suffix[2*n:], 1):
        name, operation, a, b = row
        need(operation == '+' and b == squares[i] and a in collected, 'SOS sum recurrence')
        need(name == prefix + '_sum' + str(i), 'SOS sum label')
        collected[name] = {**collected[a], b: collected[a].get(b, 0) + 1}
    expected_output = suffix[-1][0]
    need(circuit['output'] == expected_output, 'No output outside complete SOS')
    if n > 1:
        need(collected[expected_output] == dict.fromkeys(squares, 1), 'Each square occurs once')
    return len(circuit['source']) - gate_count


def leading_components(circuit):
    """Propagate FORMAL bounds and homogeneous components at those bounds.

    A zero component is retained at its existing formal bound. In particular,
    cancellation at a chosen weight NEVER lowers the bound at any gate.
    """
    ports = circuit['parameters'] + circuit['auxiliaries']
    weights = dict(zip(ports, range(2, len(ports) + 2)))
    bounds = dict.fromkeys(ports, 1)
    component = dict(weights)
    trace = []
    for name, operation, a, b in circuit['source']:
        da, ca = (bounds[a], component[a]) if type(a) is str else (0, a % MOD)
        db, cb = (bounds[b], component[b]) if type(b) is str else (0, b % MOD)
        if operation == '*':
            degree, coefficient = da + db, ca * cb
        else:
            degree = max(da, db)
            coefficient = 0
            if da == degree:
                coefficient += ca
            if db == degree:
                coefficient += cb if operation == '+' else -cb
        bounds[name], component[name] = degree, coefficient % MOD
        trace.append([name, degree, coefficient % MOD])
    out = circuit['output']
    return {
        'modulus': MOD, 'substitution_weights': weights,
        'formal_degree': bounds[out], 'nonzero_top_coefficient': component[out],
        'gate_degree_top_trace': trace,
    }


def formal_bound_regression():
    example = {
        'parameters': ['x', 'y'], 'auxiliaries': [],
        'source': [['a', '-', 'x', 'x'], ['b', '*', 'a', 'x'],
                   ['c', '+', 'b', 'y'], ['d', '*', 'x', 'x'], ['e', '+', 'c', 'd']],
        'output': 'e',
    }
    trace = leading_components(example)['gate_degree_top_trace']
    need(trace == [['a', 1, 0], ['b', 2, 0], ['c', 2, 0], ['d', 2, 4], ['e', 2, 4]],
         'Zero top components must not cause bound lowering')


def evaluate(circuit, values, modulus=None):
    env = dict(values)
    for name, operation, a, b in circuit['source']:
        aa = env[a] if type(a) is str else a
        bb = env[b] if type(b) is str else b
        result = aa + bb if operation == '+' else aa - bb if operation == '-' else aa * bb
        env[name] = result if modulus is None else result % modulus
    def value(atom):
        return env[atom] if type(atom) is str else atom
    expected = sum((value(a) - value(b)) ** 2 for a, b in circuit['comparisons'])
    if modulus is not None:
        expected %= modulus
    need(env[circuit['output']] == expected, 'Independent direct SOS evaluation')
    if modulus is None:
        need(expected >= 0, 'Integer SOS nonnegativity')
        need((expected == 0) == all(value(a) == value(b) for a, b in circuit['comparisons']),
             'Integer SOS zero iff all comparisons')
    return env


def valuation_tests(circuit):
    ports = circuit['parameters'] + circuit['auxiliaries']
    for test in range(12):
        values = {p: ((i*i + 7*i + 11*test + 3*i*test) % 7) - 3 for i, p in enumerate(ports)}
        evaluate(circuit, values)
    for test in range(32):
        values = {p: ((i+17)*(test+101)*7919 + i*i*104729 - test*test*65537) % MOD
                  for i, p in enumerate(ports)}
        evaluate(circuit, values, MOD)
    return {'signed_integer_trials': 12, 'modular_trials': 32}


def affine(rows, allowed):
    """Expand bridge rows as exact affine forms, without fixed intermediate labels."""
    forms = {name: {name: 1} for name in allowed}
    def get(atom):
        return forms[atom] if type(atom) is str else {'1': atom}
    for name, operation, a, b in rows:
        left, right = get(a), get(b)
        if operation in ('+', '-'):
            form = dict(left)
            for key, coefficient in right.items():
                form[key] = form.get(key, 0) + (coefficient if operation == '+' else -coefficient)
        else:
            need(set(left) <= {'1'} or set(right) <= {'1'}, 'Bridge is affine')
            scalar, other = (left.get('1', 0), right) if set(left) <= {'1'} else (right.get('1', 0), left)
            form = {key: scalar*coefficient for key, coefficient in other.items()}
        forms[name] = {key: value for key, value in form.items() if value}
    return forms


def check_ledger(circuit, actual, degree):
    actual['exact_degree'] = degree['formal_degree']
    actual['comparisons'] = len(circuit['comparisons'])
    if circuit['format'] == 'complete-unbounded-clean-clock-v1':
        actual['SOS_gates'] = 3 * len(circuit['comparisons']) - 1
    need(circuit['ledger'] == actual, 'Entire emitted ledger independently agrees')
    need(circuit['exact_degree_certificate'] == degree, 'Every degree-certificate field and gate trace agrees')
    need(degree['nonzero_top_coefficient'] != 0, 'Nonzero highest homogeneous component')


def textual_dag(path, circuit):
    lines = path.read_text().splitlines()
    need(lines[1] == '# Natural ports: ' + ', '.join(circuit['parameters']), 'Text natural ports')
    need(lines[2] == '# Strictly positive existential ports: ' + ', '.join(circuit['auxiliaries']), 'Text positive ports')
    rows = []
    for line in lines:
        if line.startswith('#'):
            continue
        name, equality, a, operation, b = line.split()
        need(equality == '=', 'Text assignment')
        def atom(s):
            return int(s) if s.lstrip('-').isdigit() else s
        rows.append([name, operation, atom(a), atom(b)])
    need(rows == circuit['source'], 'Text and JSON arithmetic DAGs identical')
    need(lines[-2] == '# Polynomial output: ' + circuit['output'], 'Text output')
    need(lines[-1] == '# Required equation: ' + circuit['output'] + ' = 0', 'Text equality')


def check_raw(raw):
    need(raw['parameters'] == ['x', 'y', 'T'], 'Raw interface')
    actual = dag_shape(raw)
    need(len(raw['comparisons']) == 20, 'Twenty raw comparisons')
    split = sos_tail(raw, 'sos')
    need(raw['comparisons'][-1] == ['final_positive', 'y'], 'Exact raw endpoint row')
    need(all('y' not in row for row in raw['comparisons'][:-1]), 'No other endpoint-y comparison')
    uses = [(name, side) for name, op, a, b in raw['source']
            for side, operand in [('left', a), ('right', b)] if operand == 'y']
    need(uses == [('sos_res19', 'right')], 'Raw y is used only in removed endpoint residual')
    need(not any('y' in row[2:] for row in raw['source'][:split]), 'Raw core independent of y')
    for key in ('total', 'M', 'A', 'positive_witnesses'):
        need(raw['ledger'][key] == actual[key], 'Source receipt ledger agrees')
    machine = raw['machine']
    need('s' in machine['states'] and 'h' in machine['states'] and 's' != 'h', 'Nonempty machine interface')
    need(all(row[1] != 's' and row[0] != 'h' for row in machine['instructions']), 'Separated start/halt')
    return split


def check_complete(circuit, raw, phase):
    need(circuit['format'] == 'complete-unbounded-clean-clock-v1', 'Format')
    need(circuit['source_pin'] == PIN, 'Source pin metadata')
    need(circuit['source_commit'] == 'ad634b2d10ad666260f9fdff04ec94b75169ee4b', 'Commit metadata')
    need(circuit['fixture'] == raw['name'], 'Fixture identity')
    need(circuit['parameters'] == ['x', 'Tclean'], 'Only ordinary natural input and clean time')
    need(circuit['auxiliaries'] == raw['auxiliaries'] + ['theta_positive'], 'Exactly one new positive witness')
    need(circuit['domain'] == 'x,Tclean are natural integers; all listed auxiliaries are strictly positive integers', 'Domain')
    need(circuit['removed_comparison'] == ['final_positive', 'y'], 'Deleted-row metadata')
    need(circuit['native_clock_coordinate'] == 'theta_positive', 'Native clock coordinate')
    need(circuit['forward_final_payload_coordinate'] == 'final_positive', 'Forward payload coordinate')
    need(circuit['cleaned_target_payload'] == 'x+1', 'Cleaned target metadata')
    factor = 4 if phase else 1
    need(circuit['physical_clock_factor'] == factor, 'Clock factor')
    need(circuit['model'] == ('phase4' if phase else 'native-or-spatial-block'), 'Model')
    need(circuit['source_machine'] == raw['machine'] and circuit['mapping'] == raw['mapping'], 'Source model inheritance')
    core_end = check_raw(raw)
    rename = lambda atom: 'theta_positive' if atom == 'T' else atom
    for original, emitted in zip(raw['source'][:core_end], circuit['source'][:core_end]):
        name, operation, a, b = original
        need(emitted == [name, operation, rename(a), rename(b)], 'Every raw core gate inherited exactly')
    need(circuit['comparisons'][:19] == [[rename(a), rename(b)] for a, b in raw['comparisons'][:19]],
         'All nineteen non-endpoint guards retained exactly')
    need(len(circuit['comparisons']) == 20, 'Exactly twenty complete comparisons')
    clean_end = sos_tail(circuit, 'clean_sos')
    bridge = circuit['source'][core_end:clean_end]
    need(len(bridge) == 6 + phase, 'Only paid bridge gates outside inherited core and SOS')
    need(sum(row[1] == '*' for row in bridge) == 2 + phase, 'Paid bridge multiplication count')
    need(sum(row[1] != '*' for row in bridge) == 4, 'Paid bridge addition count')
    forms = affine(bridge, ['final_positive', 'x', 'theta_positive'])
    endpoint, requested_time = circuit['comparisons'][-1]
    need(requested_time == 'Tclean' and endpoint == bridge[-1][0], 'Clean time comparison')
    expected = {'final_positive': 192*factor, 'x': 192*factor, 'theta_positive': 2*factor, '1': 208*factor}
    need(forms[endpoint] == expected, 'Exact clean bridge affine identity')
    actual = dag_shape(circuit)
    degree = leading_components(circuit)
    check_ledger(circuit, actual, degree)
    total, mults, adds, witnesses, d = NATIVE[raw['name']]
    need((actual['total'], actual['M'], actual['A'], actual['positive_witnesses'], actual['exact_degree'])
         == (total+phase, mults+phase, adds, witnesses, d), 'Expected complete arithmetic counts')
    need('T' not in circuit['parameters'] + circuit['auxiliaries'] and 'y' not in circuit['parameters'] + circuit['auxiliaries'],
         'No hidden raw input ports')
    tests = valuation_tests(circuit)
    return {
        **actual, **tests, 'raw_core_gates_retained': core_end,
        'retained_raw_comparisons': 19, 'new_time_comparisons': 1,
        'affine_clock': expected, 'highest_component_modulus': MOD,
        'highest_component_value': degree['nonzero_top_coefficient'],
        'zero_top_trace_entries_without_bound_reduction': sum(row[2] == 0 for row in degree['gate_degree_top_trace']),
    }


def check_zero(circuit, phase):
    factor = 4 if phase else 1
    need(circuit['format'] == 'zero-step-clean-clock-v1', 'Separate zero-step format')
    need(circuit['parameters'] == ['x', 'Tclean'] and circuit['auxiliaries'] == [], 'Zero-step ports')
    need(circuit['physical_clock_factor'] == factor, 'Zero-step factor')
    need(circuit['comparisons'] == [['zero_time', 'Tclean']], 'Zero-step sole comparison')
    bridge_end = sos_tail(circuit, 'clean_sos')
    need(bridge_end == 2, 'Zero-step two-gate bridge')
    forms = affine(circuit['source'][:bridge_end], ['x'])
    need(forms['zero_time'] == {'x': 384*factor, '1': 400*factor}, 'Exact zero-step specialization')
    actual = dag_shape(circuit)
    degree = leading_components(circuit)
    check_ledger(circuit, actual, degree)
    need((actual['total'], actual['M'], actual['A'], actual['positive_witnesses'], actual['exact_degree']) == (4, 2, 2, 0, 2),
         'Zero-step ledger')
    tests = valuation_tests(circuit)
    for x in range(101):
        time = factor*(384*x+400)
        for offset in (-1, 0, 1):
            env = evaluate(circuit, {'x': x, 'Tclean': time+offset})
            need(env[circuit['output']] == offset*offset, 'Zero-step exact/near-miss zeros')
    return {**actual, **tests, 'endpoint_and_near_miss_cases': 303,
            'affine_clock': forms['zero_time'], 'highest_component_modulus': MOD,
            'highest_component_value': degree['nonzero_top_coefficient']}


def mutation_regressions(circuit, raw):
    changes = []
    def reject(label, edit):
        other = copy.deepcopy(circuit)
        edit(other)
        try:
            check_complete(other, raw, False)
        except (ValueError, KeyError, IndexError):
            changes.append(label)
        else:
            raise ValueError('Mutation escaped: ' + label)
    reject('omitted positive witness', lambda c: c['auxiliaries'].pop(0))
    reject('undeclared operand', lambda c: c['source'][0].__setitem__(3, 'missing'))
    reject('modified raw gate', lambda c: c['source'][0].__setitem__(2, 6))
    reject('removed retained comparison', lambda c: c['comparisons'].pop(7))
    reject('changed clean affine clock', lambda c: c['source'][-60].__setitem__(3, 17))
    reject('extra dead gate', lambda c: c['source'].insert(0, ['unused', '+', 'x', 0]))
    reject('undercounted full ledger', lambda c: c['ledger'].__setitem__('total', c['ledger']['total']-1))
    reject('false output degree certificate', lambda c: c['exact_degree_certificate'].__setitem__('formal_degree', 0))
    return changes


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--expect', type=Path)
    args = parser.parse_args()
    root = args.root
    source_path = root / 'source/three_mass_unbounded_interface.json'
    need(sha(source_path.read_bytes()) == PIN, 'Authenticated literal source receipt')
    source = read_json(source_path)
    raw = {f['name']: f for f in source['fixtures']}
    need(set(raw) == set(NATIVE), 'Exactly four source fixtures')
    need(all(MOD % d for d in range(2, 1001)), 'Prime certificate modulus')
    formal_bound_regression()
    results, hashes, loaded = {}, {}, {}
    for fixture in NATIVE:
        for phase in (False, True):
            stem = fixture + ('-phase4' if phase else '-native')
            path = root / 'circuits' / (stem + '.json')
            circuit = read_json(path)
            loaded[stem] = circuit
            results[stem] = check_complete(circuit, raw[fixture], phase)
            text_path = path.with_suffix('.dag.txt')
            textual_dag(text_path, circuit)
            for p in (path, text_path):
                hashes[str(p.relative_to(root))] = sha(p.read_bytes())
        native, phase4 = loaded[fixture+'-native'], loaded[fixture+'-phase4']
        split = sos_tail(native, 'clean_sos')
        need(phase4['source'][:split] == native['source'][:split], 'Phase4 inherits full native pre-finalizer')
        need(phase4['source'][split] == ['clean_phase_time', '*', 4, 'clean_native_time'], 'Only one phase4 gate')
        need(phase4['comparisons'][:19] == native['comparisons'][:19], 'Phase4 unchanged guards')
    for phase in (False, True):
        stem = 'zero-step-' + ('phase4' if phase else 'native')
        path = root / 'circuits' / (stem + '.json')
        circuit = read_json(path)
        results[stem] = check_zero(circuit, phase)
        hashes[str(path.relative_to(root))] = sha(path.read_bytes())
    actual_files = {str(p.relative_to(root)) for p in (root/'circuits').iterdir() if p.is_file()}
    need(actual_files == set(hashes), 'Exactly all eighteen emitted circuit artifacts audited')
    manifest = read_json(root / 'receipts/emission.json')
    need(manifest['pinned_input'] == {'source/three_mass_unbounded_interface.json': PIN}, 'Emission input hash')
    need(manifest['emitted_files'] == hashes, 'Emission manifest hashes independently verified')
    for stem in results:
        expected_ledger = read_json(root/'circuits'/(stem+'.json'))['ledger']
        need(manifest['ledgers'][stem] == expected_ledger, 'Emission manifest ledger')
    mutations = mutation_regressions(loaded['nop-native'], raw['nop'])
    receipt = {
        'status': 'PASS', 'audit_format': 'independent-clean-clock-circuit-audit-v1',
        'authenticated_source_receipt_sha256': PIN,
        'checker_sha256': sha(Path(__file__).read_bytes()),
        'emitter_or_source_python_imported_or_executed': False,
        'checked_artifacts': hashes, 'circuits': results,
        'totals': {
            'complete_circuits': 8, 'separate_zero_step_circuits': 2,
            'emitted_arithmetic_gates_audited': sum(r['total'] for r in results.values()),
            'raw_core_gate_identities_checked': sum(r.get('raw_core_gates_retained', 0) for r in results.values()),
            'retained_raw_comparison_identities_checked': 8*19,
            'complete_SOS_rows_checked': 8*20+2,
            'signed_integer_SOS_trials': 10*12,
            'modular_SOS_trials': 10*32,
            'zero_step_exact_and_near_miss_evaluations': 606,
        },
        'formal_bound_zero_component_regression': 'PASS',
        'deliberate_mutations_rejected': mutations,
        'proof_scope': [
            'Exact literal arithmetic DAG inheritance, complete SOS identities, full ledgers and exact polynomial degrees are independently audited.',
            'Clean clock equivalence is conditional on the authenticated raw first-halting/native theorem and the previously established cleanup/reverse-lift theorem.',
            'Arbitrary signed and modular evaluations are algebraic tests, not positive native Pell witness tuples.',
            'No native Pell witness tuple is numerically materialized; no new universal machine, ordinary-input loader, or universal operation bound is established.',
        ],
    }
    output = json.dumps(receipt, indent=2, sort_keys=True) + '\n'
    if args.expect:
        need(args.expect.read_text() == output, 'Independent deterministic audit replay')
    else:
        (root/'audit/independent_emitted_circuit_audit.json').write_text(output)
    print(json.dumps({'status': 'PASS', 'mode': 'replay' if args.expect else 'audit',
                      'totals': receipt['totals'],
                      'exact_degrees_and_top_components': {k: [v['exact_degree'], v['highest_component_value']] for k, v in results.items()}}, sort_keys=True))


if __name__ == '__main__':
    main()
