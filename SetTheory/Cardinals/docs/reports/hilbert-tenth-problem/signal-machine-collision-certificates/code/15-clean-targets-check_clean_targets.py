#!/usr/bin/env python3
"""Independent wrapper checker; the exporter is deliberately not imported."""
from pathlib import Path
import argparse
import json
import sys
sys.path.insert(0, str(Path(__file__).resolve().parent / 'vendor'))
import checker as forward_checker


def check(cert, witness):
    def need(test, message):
        if not test: raise ValueError(message)
    def strict(obj):
        if obj is None or type(obj) in (str, int): return
        if type(obj) is list:
            for v in obj: strict(v)
        elif type(obj) is dict:
            need(all(type(k) is str for k in obj), 'nonstring key')
            for v in obj.values(): strict(v)
        else: raise ValueError('JSON data requires strict integers, not bool or float')
    strict(cert); strict(witness)
    need(cert['format'] == 'three-mass-clean-exact-target-v1', 'unknown format')
    need(cert['domain'] == 'nonnegative integers', 'incorrect domain')
    forward = cert['forward_certificate']
    need(forward.get('clock_scale', 1) == 1 and forward['output_spec'] is None
         and forward['time_spec'] is None, 'forward certificate must have no endpoints and native clock')
    need(set(witness) == set(cert['variables']), 'witness names disagree')
    need(all(type(v) is int and v >= 0 for v in witness.values()), 'witness is not natural')
    result = forward_checker.check(forward, {k: witness[k] for k in forward['variables']})
    machine, q0 = forward['machine'], forward['initial_state']
    ins = machine['instructions']
    need(not any(i['target'] == q0 for i in ins), 'source initial state is not fresh')
    inverse = {'inc': 'dec', 'dec': 'inc', 'zero': 'zero', 'positive': 'positive', 'nop': 'nop'}
    cleaned_ins = [{'source': 'F:'+i['source'], 'target': 'F:'+i['target'],
                    'operation': i['operation'], 'counter': i['counter']} for i in ins]
    cleaned_ins += [{'source': 'B:'+i['target'], 'target': 'B:'+i['source'],
                     'operation': inverse[i['operation']], 'counter': i['counter']} for i in ins]
    cleaned_ins += [{'source': 'F:'+machine['halt'], 'target': 'B:'+machine['halt'],
                     'operation': 'nop', 'counter': 0},
                    {'source': 'B:'+q0, 'target': 'H', 'operation': 'nop', 'counter': 0}]
    cleaned = {'states': ['F:'+q for q in machine['states']]+['B:'+q for q in machine['states']]+['H'],
               'halt': 'H', 'instructions': cleaned_ins}
    need(cert['cleaned_machine'] == cleaned, 'incorrect cleaned machine')
    need(cert['cleaned_initial_state'] == 'F:'+q0, 'incorrect cleaned initial state')
    def ledger(m):
        return {'states': len(m['states']), 'instructions': len(m['instructions']),
                'instruction_modulus': len(m['instructions'])+1,
                'arithmetic_instructions': sum(i['operation'] in ('inc', 'dec') for i in m['instructions']),
                'expanded_branches': len(m['instructions'])+sum(i['operation'] == 'zero' and i['counter'] == 1 for i in m['instructions'])}
    need(cert['source_ledger'] == ledger(machine), 'incorrect source counts')
    need(cert['cleaned_source_ledger'] == ledger(cleaned), 'incorrect cleaned source counts')
    h = forward['horizon']; scale = {'native': 1, 'spatial-radius-one': 1, 'phase-radius-one': 4}.get(cert['model'])
    need(scale is not None and cert['clock_scale'] == scale, 'incorrect model/clock')
    need(cert['cleaned_source_horizon'] == 2*h+2, 'incorrect cleaned horizon')
    need(cert['initial_N'] == forward['initial_N'] and cert['exact_target_N'] == forward['initial_N']
         and cert['exact_target_state'] == 'H', 'incorrect input-dependent exact target')
    plus, times, const, minus = forward_checker.plus, forward_checker.times, forward_checker.const, forward_checker.minus
    clock = times(plus(times(forward['physical_time'], 2), times(forward['final_N'], 192),
                       times(forward['initial_N'], 192), const(16)), scale)
    need(cert['physical_time'] == clock, 'incorrect cleaned physical-time form')
    variables, outputs, squares = list(forward['variables']), [], list(forward['squares'])
    spec = cert['time_spec']
    if spec is not None:
        need(type(spec) is dict and spec.get('mode') in ('fixed', 'free'), 'bad time mode')
        if spec['mode'] == 'fixed':
            need(not set(spec)-{'mode', 'value'} and type(spec.get('value')) is int and spec['value'] >= 0, 'bad fixed time')
            target = const(spec['value'])
        else:
            need(not set(spec)-{'mode', 'name'}, 'extra time fields')
            name = spec.get('name', 'cleaned_physical_time')
            need(type(name) is str and name and name not in variables, 'bad output name')
            outputs.append(name); variables.append(name); target = {name: 1}
        squares.append({'label': 'terminal:cleaned-physical-time', 'affine': minus(clock, target)})
    need(cert['variables'] == variables and cert['output_variables'] == outputs
         and cert['input_variables'] == forward['input_variables'], 'incorrect variable list')
    need(cert['squares'] == squares and cert['products'] == forward['products'], 'incorrect polynomial presentation')
    fl = forward['ledger']
    expected = {'forward_source_horizon': h, 'cleaned_source_horizon': 2*h+2,
                'branch_count': fl['branch_count'], 'core_variables': fl['core_variables'],
                'input_variables': fl['input_variables'], 'loader_variables': fl['loader_variables'],
                'output_variables': len(outputs), 'total_variables': len(variables),
                'core_squares': 3*h+1, 'loader_squares': fl['loader_squares'],
                'endpoint_squares': int(spec is not None), 'total_squares': len(squares),
                'product_slots': fl['product_slots'], 'maximum_degree': 2}
    need(cert['ledger'] == expected, 'incorrect compact ledger')
    ev = forward_checker.ev
    terms = [ev(s['affine'], witness)**2 for s in squares]
    terms += [ev(p['left'], witness)*ev(p['right'], witness) for p in cert['products']]
    need(all(v >= 0 for v in terms) and sum(terms) == 0, 'polynomial is not zero')
    if 'expanded_polynomial' in cert:
        expanded = {}
        pairs = [(s['affine'], s['affine']) for s in squares]+[(p['left'], p['right']) for p in cert['products']]
        for a, b in pairs:
            for x, c in a.items():
                for y, d in b.items():
                    monomial = tuple(sorted(k for k in (x, y) if k))
                    expanded[monomial] = expanded.get(monomial, 0)+c*d
        literal = [{'monomial': list(k), 'coefficient': v} for k, v in sorted(expanded.items()) if v]
        need(cert['expanded_polynomial'] == literal, 'incorrect literal expansion')
    ft = result['source_trace']; theta = result['physical_time']
    n0, nh = ft[0]['N'], ft[-1]['N']; switch_h = 192*nh+8; switch_0 = 192*n0+8
    trace = []
    for row in ft:
        trace.append({'step': len(trace), 'state': 'F:'+row['state'], 'N': row['N'], 'microtime': scale*row['microtime']})
    for row in reversed(ft):
        trace.append({'step': len(trace), 'state': 'B:'+row['state'], 'N': row['N'],
                      'microtime': scale*(2*theta+switch_h-row['microtime'])})
    total = scale*(2*theta+switch_h+switch_0)
    trace.append({'step': len(trace), 'state': 'H', 'N': n0, 'microtime': total})
    need(total == ev(clock, witness) and len(trace) == 2*h+3, 'decoded clock/horizon mismatch')
    return {'status': 'passed', 'forward_source_trace': ft, 'cleaned_source_trace': trace,
            'forward_physical_time': theta, 'physical_time': total, 'exact_target_state': 'H',
            'exact_target_N': n0, 'target_gap': (3 if cert['model'] == 'spatial-radius-one' else 12)*n0,
            'ledger': expected}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate'); p.add_argument('witness'); p.add_argument('--receipt')
    args = p.parse_args()
    result = check(json.loads(Path(args.certificate).read_text()), json.loads(Path(args.witness).read_text()))
    text = json.dumps(result, indent=2)+'\n'
    if args.receipt: Path(args.receipt).write_text(text)
    else: print(text, end='')

if __name__ == '__main__': main()
