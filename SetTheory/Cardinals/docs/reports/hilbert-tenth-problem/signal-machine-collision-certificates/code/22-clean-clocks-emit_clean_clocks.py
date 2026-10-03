#!/usr/bin/env python3
"""Data-only complete circuit emitter. Standard library; no author code imports.

The source receipt is authenticated before reading its literal arithmetic DAGs.
This script does not evaluate foreign Python, install packages, or access a repo.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE = 'source/three_mass_unbounded_interface.json'
SOURCE_PIN = 'fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e'
COMMIT = 'ad634b2d10ad666260f9fdff04ec94b75169ee4b'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def serialization(data):
    return (json.dumps(data, indent=2, sort_keys=True) + '\n').encode()

def finalizer(pairs, prefix='clean_sos'):
    rows = []
    squares = []
    for i, (a, b) in enumerate(pairs):
        r, s = f'{prefix}_res{i}', f'{prefix}_sq{i}'
        rows += [[r, '-', a, b], [s, '*', r, r]]
        squares.append(s)
    out = squares[0]
    for i, term in enumerate(squares[1:], 1):
        new = f'{prefix}_sum{i}'
        rows.append([new, '+', out, term])
        out = new
    return rows, out

def inspect(rows, output, parameters, auxiliaries):
    inputs = parameters + auxiliaries
    require(len(set(inputs)) == len(inputs), 'Distinct ports')
    degrees = dict.fromkeys(inputs, 1)
    weights = {name: i + 2 for i, name in enumerate(inputs)}
    tops = dict(weights)
    modulus = 1000003
    gates = {}
    counts = Counter()
    constants = set()
    trace = []
    for name, op, a, b in rows:
        require(type(name) is str and name not in degrees and op in ('+', '-', '*'), 'Fresh arithmetic gate')
        require(all(type(x) is int or type(x) is str and x in degrees for x in (a, b)), 'Closed typed DAG')
        da = degrees[a] if type(a) is str else 0
        db = degrees[b] if type(b) is str else 0
        ca = tops[a] if type(a) is str else a % modulus
        cb = tops[b] if type(b) is str else b % modulus
        d = da + db if op == '*' else max(da, db)
        c = ca * cb if op == '*' else (ca if da == d else 0) + (1 if op == '+' else -1) * (cb if db == d else 0)
        degrees[name], tops[name] = d, c % modulus
        gates[name] = [op, a, b]
        counts['M' if op == '*' else 'A'] += 1
        constants.update(x for x in (a, b) if type(x) is int)
        trace.append([name, d, c % modulus])
    live, live_inputs, todo = set(), set(), [output]
    while todo:
        n = todo.pop()
        if type(n) is not str:
            continue
        if n in gates and n not in live:
            live.add(n)
            todo.extend(gates[n][1:])
        elif n in inputs:
            live_inputs.add(n)
    require(live == set(gates), 'All gates live')
    require(live_inputs == set(inputs), 'All supplied coordinates live')
    require(tops[output] != 0, 'Nonzero leading coefficient certifies exact degree')
    return dict(total=len(rows), M=counts['M'], A=counts['A'], positive_witnesses=len(auxiliaries), natural_parameters=len(parameters), exact_degree=degrees[output], integer_literals=sorted(constants), all_gates_live=True, all_coordinates_live=True), dict(modulus=modulus, substitution_weights=weights, formal_degree=degrees[output], nonzero_top_coefficient=tops[output], gate_degree_top_trace=trace)

def authenticate_raw(f):
    pairs = f['comparisons']
    require(len(pairs) == 20 and pairs[-1] == ['final_positive', 'y'], 'Exact paid raw endpoint row')
    require(f['parameters'] == ['x', 'y', 'T'], 'Known natural interface')
    start = next(i for i, r in enumerate(f['source']) if r[0] == 'sos_res0')
    expected, output = finalizer(pairs, 'sos')
    require(f['source'][start:] == expected and f['output'] == output, 'Complete raw SOS, no omitted row')
    ledger, _ = inspect(f['source'], f['output'], f['parameters'], f['auxiliaries'])
    for key in ('total', 'M', 'A', 'positive_witnesses'):
        require(ledger[key] == f['ledger'][key], 'Authenticated raw ledger')
    require(ledger['exact_degree'] == f['ledger']['degree_upper_bound'], 'Raw degree comparison')
    machine = f['machine']
    require('s' in machine['states'] and 'h' in machine['states'] and 's' != 'h', 'Nonempty source')
    require(all(r[1] != 's' and r[0] != 'h' for r in machine['instructions']), 'Fresh start and terminal halt')
    require(not any('y' in r[2:] for r in f['source'][:start]), 'Eliminated endpoint occurs only in deleted comparison')
    return f['source'][:start]

def build(f, phase=False):
    core = authenticate_raw(f)
    rename = lambda x: 'theta_positive' if x == 'T' else x
    rows = [[n, op, rename(a), rename(b)] for n, op, a, b in core]
    pairs = [[rename(a), rename(b)] for a, b in f['comparisons'][:-1]]
    bridge = [
        ['clean_payload_sum0', '+', 'final_positive', 'x'],
        ['clean_payload_sum', '+', 'clean_payload_sum0', 1],
        ['clean_endpoint_ticks', '*', 192, 'clean_payload_sum'],
        ['clean_forward_reverse_ticks', '*', 2, 'theta_positive'],
        ['clean_partial_time', '+', 'clean_endpoint_ticks', 'clean_forward_reverse_ticks'],
        ['clean_native_time', '+', 'clean_partial_time', 16],
    ]
    rows += bridge
    endpoint = 'clean_native_time'
    if phase:
        rows.append(['clean_phase_time', '*', 4, endpoint])
        endpoint = 'clean_phase_time'
    pairs.append([endpoint, 'Tclean'])
    finish, out = finalizer(pairs)
    rows += finish
    aux = f['auxiliaries'] + ['theta_positive']
    params = ['x', 'Tclean']
    ledger, degree = inspect(rows, out, params, aux)
    ledger['comparisons'] = len(pairs)
    ledger['SOS_gates'] = len(finish)
    return dict(format='complete-unbounded-clean-clock-v1', fixture=f['name'], model='phase4' if phase else 'native-or-spatial-block', source_pin=SOURCE_PIN, source_commit=COMMIT, parameters=params, auxiliaries=aux, domain='x,Tclean are natural integers; all listed auxiliaries are strictly positive integers', source_machine=f['machine'], mapping=f['mapping'], source=rows, output=out, comparisons=pairs, ledger=ledger, exact_degree_certificate=degree, removed_comparison=['final_positive','y'], native_clock_coordinate='theta_positive', forward_final_payload_coordinate='final_positive', cleaned_target_payload='x+1', physical_clock_factor=4 if phase else 1, scope='Fixed nonuniversal source. No horizon parameter. No ordinary-input universal loader. Native Pell witnesses remain inherited existential dependencies.')

def zero_step(phase=False):
    factor = 4 if phase else 1
    rows = [['zero_scaled_input', '*', 384 * factor, 'x'], ['zero_time', '+', 'zero_scaled_input', 400 * factor]]
    pairs = [['zero_time', 'Tclean']]
    finish, out = finalizer(pairs)
    rows += finish
    ledger, degree = inspect(rows, out, ['x','Tclean'], [])
    ledger['comparisons'] = 1
    return dict(format='zero-step-clean-clock-v1', parameters=['x','Tclean'], auxiliaries=[], source=rows, output=out, comparisons=pairs, ledger=ledger, exact_degree_certificate=degree, physical_clock_factor=factor, scope='Separate initially halted isolated source. Two NOP cleanup bridges. Not a nonempty residue-history certificate.')

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', action='store_true', help='Rebuild in memory and compare all deterministic emitted bytes')
    args = ap.parse_args()
    data = (ROOT / SOURCE).read_bytes()
    require(digest(data) == SOURCE_PIN, 'Pinned upstream receipt bytes')
    raw = json.loads(data)
    outputs = {}
    summary = {}
    for f in raw['fixtures']:
        for phase in (False, True):
            p = build(f, phase)
            name = f['name'] + ('-phase4' if phase else '-native')
            outputs[f'circuits/{name}.json'] = serialization(p)
            lines = ['# Complete literal arithmetic DAG; every listed +, -, * costs one operation.', '# Natural ports: ' + ', '.join(p['parameters']), '# Strictly positive existential ports: ' + ', '.join(p['auxiliaries'])]
            lines += [f'{n} = {a} {op} {b}' for n, op, a, b in p['source']]
            lines += ['# Polynomial output: ' + p['output'], '# Required equation: ' + p['output'] + ' = 0']
            outputs[f'circuits/{name}.dag.txt'] = ('\n'.join(lines) + '\n').encode()
            summary[name] = p['ledger']
    for phase in (False, True):
        name = 'zero-step-' + ('phase4' if phase else 'native')
        p = zero_step(phase)
        outputs[f'circuits/{name}.json'] = serialization(p)
        summary[name] = p['ledger']
    manifest = dict(format='clean-clock-emission-receipt-v1', pinned_input={SOURCE:SOURCE_PIN}, emitted_files={name:digest(data) for name,data in outputs.items()}, ledgers=summary, third_party_python_executed=False)
    outputs['receipts/emission.json'] = serialization(manifest)
    for name, content in outputs.items():
        destination = ROOT / name
        if args.check:
            require(destination.read_bytes() == content, 'Exact replay: ' + name)
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(content)
    print(json.dumps(dict(status='PASS', mode='replay' if args.check else 'emit', ledgers={k:{a:v[a] for a in ('M','A','total','positive_witnesses','exact_degree')} for k,v in summary.items()}), sort_keys=True))

if __name__ == '__main__':
    main()
