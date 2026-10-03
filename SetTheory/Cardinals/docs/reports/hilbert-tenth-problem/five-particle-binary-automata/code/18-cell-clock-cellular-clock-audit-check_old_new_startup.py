#!/usr/bin/env python3
"""Independently traverse frozen five-counter startups and charge prime macros.

Uses only this audit's previously verified macro coefficient implementation.
No producer executable is imported; no old full literal path or CA is run.
"""
from pathlib import Path
from collections import defaultdict
import hashlib
import json
import sys

from check_ca_clock import macro_components

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
from verify_pins import verify_inputs
from baseline_support import regenerated_baseline
PRIMES = (2, 3, 5, 7, 11)


def require(ok, detail):
    if not ok:
        raise RuntimeError(detail)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(root, label):
    machine = json.loads((root / 'reversible5.json').read_text())
    source = json.loads((root / 'source.json').read_text())
    rows = defaultdict(list)
    for e in machine['rows']:
        rows[e['source']].append(e)
    moving_branches = sum(bool(e['delta']) for e in source['branches'])
    D = 2 * len(source['controls']) + 4 * moving_branches
    J = source['class_cut']
    lam = 72 * D + 115 + 4 * J
    require(lam == 36684691, 'Compiler clock coefficient')
    q, values = machine['start'], [0] * 5
    trace, totals = [], [0, 0, 0]
    while q != 'tm_A0_pop0':
        options = []
        for e in rows[q]:
            v = values[e['counter']]
            s = e['symbol']
            if s in ('+', '0') or (v == 0 if s == 'Z' else v > 0):
                options.append(e)
        require(len(options) == 1, ('Five-counter determinism', q, values))
        row = options[0]
        N = 1
        for prime, exponent in zip(PRIMES, values):
            N *= prime ** exponent
        prime, symbol = PRIMES[row['counter']], row['symbol']
        if symbol in ('-', 'P', 'Z'):
            require((N % prime == 0) == (symbol != 'Z'), 'Encoded operation enabledness')
        components = macro_components(symbol, prime, N)
        for i, value in enumerate(components):
            totals[i] += value
        clock = lam * components[0] + components[1] + components[2]
        trace.append({'step': len(trace), 'control': q, 'counters': values.copy(),
                      'row': row['name'], 'symbol': symbol, 'prime': prime,
                      'encoded_input_N': N, 'macro_components_moves_variation_tests': list(components),
                      'derived_CA_clock': clock})
        values[row['counter']] += 1 if symbol == '+' else -1 if symbol == '-' else 0
        require(min(values) >= 0, 'Natural output')
        q = row['target']
        require(len(trace) < 1000, 'Startup finite-check bound')
    theta = lam * totals[0] + totals[1] + totals[2]
    require(theta == sum(r['derived_CA_clock'] for r in trace), 'Clock summation agreement')
    return {'source': label, 'source_sha256': sha(root / 'source.json'),
            'five_counter_source_sha256': sha(root / 'reversible5.json'),
            'five_counter_rows_executed': len(trace), 'final_control': q,
            'final_counters': values, 'lambda': lam,
            'predicted_literal_moving_rows': totals[0],
            'predicted_total_square_variation': totals[1],
            'predicted_literal_zero_update_rows': totals[2],
            'predicted_literal_total_rows': totals[0] + totals[2],
            'derived_CA_clock': theta}, trace


def compare(baseline):
    verify_inputs()
    results = [run(baseline, 'literal-reversible-source-20261003'),
               run(ROOT, 'reversible-initialization-optimization-20261003')]
    old, new = [r[0] for r in results]
    require((old['five_counter_rows_executed'], old['final_counters'], old['derived_CA_clock']) ==
            (142, [0, 0, 0, 15, 0], 126594455831808973674445902), 'Old result')
    require((new['five_counter_rows_executed'], new['final_counters'], new['derived_CA_clock']) ==
            (24, [0, 0, 0, 0, 0], 1394018396), 'New result')
    trace_path = HERE / 'old-new-five-row-traces.json'
    trace_path.write_text(json.dumps({r['source']: trace for r, trace in results}, indent=2) + '\n')
    receipt = {'status': 'PASS', 'mode_policy': 'Executed separately under normal and -O by run_checks.py',
               'scope': 'Actual five-counter rows traversed; independent whole-prime coefficient sums. Predicted literal row counts and CA clocks were not executed.',
               'cases': [old, new], 'checker_sha256': sha(Path(__file__)),
               'independent_macro_checker_sha256': sha(HERE / 'check_ca_clock.py'),
               'trace_file': trace_path.name, 'trace_sha256': sha(trace_path)}
    output = HERE / 'old-new-startup-receipt.json'
    output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


def main():
    with regenerated_baseline() as baseline:
        compare(baseline)


if __name__ == '__main__':
    main()
