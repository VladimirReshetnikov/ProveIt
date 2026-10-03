#!/usr/bin/env python3
"""Independent natural-witness/semantic checker, not importing the exporter.

The checker re-derives every core expression, gate and clock from the serialized
source branches; validates exact structure and the ledger; checks P=0; then
reconstructs all source configurations and microtime from selected instructions.
"""
import argparse
import json
from pathlib import Path


def plus(*xs):
    z = {}
    for x in xs:
        for k, v in x.items(): z[k] = z.get(k, 0)+v
    return {k: v for k, v in z.items() if v}
def times(x, c): return {k: v*c for k, v in x.items() if v*c}
def const(n): return {'': n} if n else {}
def variable(x): return {x: 1}
def minus(x, y): return plus(x, times(y, -1))
def ev(x, w): return x.get('', 0)+sum(v*w[k] for k, v in x.items() if k)

def check(cert, witness):
    def require(ok, message):
        if not ok: raise ValueError(message)
    def strict_json(value):
        if value is None or type(value) in (str, int): return
        if type(value) is list:
            for item in value: strict_json(item)
        elif type(value) is dict:
            require(all(type(k) is str for k in value), 'nonstring serialized key')
            for item in value.values(): strict_json(item)
        else: raise ValueError('serialized numeric values must be strict integers, never booleans or floats')
    strict_json(cert)
    require(cert['format'] == 'three-mass-source-horizon-v1', 'unsupported format')
    require(cert['domain'] == 'nonnegative integers', 'wrong domain')
    clock_scale = cert.get('clock_scale', 1)
    require(type(clock_scale) is int and clock_scale in (1, 4), 'invalid clock_scale: expected 1 or 4')
    h, machine = cert['horizon'], cert['machine']
    states, halt, insns = machine['states'], machine['halt'], machine['instructions']
    require(type(h) is int and h >= 0, 'invalid horizon')
    require(all(type(q) is str and q for q in states) and type(halt) is str
            and len(states) == len(set(states)) and halt in states and cert['initial_state'] in states,
            'invalid state set')
    for ins in insns:
        require(ins['source'] in states and ins['target'] in states and ins['source'] != halt,
                'invalid source instruction endpoints')
        require(ins['operation'] in ('inc', 'dec', 'nop', 'zero', 'positive') and type(ins['counter']) is int and ins['counter'] in (0, 1),
                'invalid operation')
    for field in ('source', 'target'):
        for q in states:
            group = [i for i in insns if i[field] == q]
            if len(group) > 1:
                require(all(i['operation'] in ('zero', 'positive') for i in group)
                        and len({i['counter'] for i in group}) == 1
                        and len({i['operation'] for i in group}) == len(group), 'unseparated or overlapping source')
    branches = []
    for index, ins in enumerate(insns):
        p = 2 if ins['counter'] == 0 else 3
        residues = range(1, p) if ins['operation'] == 'zero' else [0]
        for r in residues:
            branches.append({'instruction': index, 'source': ins['source'], 'target': ins['target'],
                             'operation': ins['operation'], 'prime': p, 'residue': r})
    require(cert['branches'] == branches, 'incorrect expanded branches')
    B = len(branches)
    variables, inputs, outputs, squares, products, steps, loader = [], [], [], [], [], [], {}
    def reg(name, role):
        require(isinstance(name, str) and name and name not in variables, 'duplicate variable')
        variables.append(name)
        if role == 'input': inputs.append(name)
        if role == 'output': outputs.append(name)
        return variable(name)
    def square(label, a): squares.append({'label': label, 'affine': a})
    spec = cert['input_spec']
    if spec['mode'] == 'fixed_raw':
        require(type(spec['N']) is int and spec['N'] >= 1, 'invalid raw N')
        start = const(spec['N'])
    elif spec['mode'] == 'free_raw':
        start = plus(const(1), reg(spec.get('name', 'raw_input_minus_one'), 'input'))
    elif spec['mode'] == 'bounded_counters':
        A, C = spec['A'], spec['B']
        require(type(A) is int and type(C) is int and A >= 0 and C >= 0, 'invalid input bounds')
        counters = []
        for k in ('a', 'b'):
            value = spec.get(k)
            if value is None: counters.append(reg(spec.get(k+'_name', 'input_'+k), 'input'))
            else:
                require(type(value) is int and value >= 0, 'invalid counter input')
                counters.append(const(value))
        sels, fa, fb, start = [], {}, {}, {}
        for a in range(A+1):
            for b in range(C+1):
                s = reg(f'load_{a}_{b}', 'loader'); sels.append(s)
                fa, fb, start = plus(fa, times(s, a)), plus(fb, times(s, b)), plus(start, times(s, 2**a*3**b))
        square('loader:one-hot', minus(plus(*sels), const(1)))
        square('loader:counter-a', minus(counters[0], fa))
        square('loader:counter-b', minus(counters[1], fb))
        loader = {'selector_count': (A+1)*(C+1), 'square_count': 3,
                  'counter_a': counters[0], 'counter_b': counters[1]}
    else: raise ValueError('unknown input mode')
    prevN, prevQ, physical = start, const(states.index(cert['initial_state'])), {}
    for t in range(h):
        local, sels = [], []
        for j, b in enumerate(branches):
            en, un = f'e_{t}_{j}', f'u_{t}_{j}'
            e, u = reg(en, 'witness'), reg(un, 'witness'); sels.append(e)
            p, op, base = b['prime'], b['operation'], plus(e, u)
            if op == 'inc': old, new = base, times(base, p)
            elif op == 'dec': old, new = times(base, p), base
            elif op == 'positive': old = new = times(base, p)
            elif op == 'zero': old = new = plus(times(u, p), times(e, b['residue']))
            else: old = new = base
            if op == 'inc': ticks = plus(times(old, 108), times(new, 96), times(e, 8))
            elif op == 'dec': ticks = plus(times(old, 96), times(new, 108), times(e, 8))
            else: ticks = plus(times(old, 192), times(e, 8))
            local.append({'branch': j, 'e': en, 'u': un, 'old': old, 'new': new, 'ticks': ticks})
        es = plus(*sels)
        sourceQ = plus(*(times(sels[j], states.index(b['source'])) for j,b in enumerate(branches)))
        targetQ = plus(*(times(sels[j], states.index(b['target'])) for j,b in enumerate(branches)))
        oldN = plus(*(l['old'] for l in local)); newN = plus(*(l['new'] for l in local))
        square(f'step-{t}:one-hot', minus(es, const(1)))
        square(f'step-{t}:control', minus(sourceQ, prevQ))
        square(f'step-{t}:value', minus(oldN, prevN))
        for j, l in enumerate(local):
            products.append({'label': f'step-{t}:inactive-{j}', 'left': minus(es, sels[j]),
                             'right': plus(sels[j], variable(l['u']))})
        physical = plus(physical, *(l['ticks'] for l in local))
        prevN, prevQ = newN, targetQ
        steps.append(local)
    square('terminal:halt', minus(prevQ, const(states.index(halt))))
    physical = times(physical, clock_scale)
    for endpoint, default, expr, label in ((cert['output_spec'], 'output_N', prevN, 'terminal:output-N'),
                                          (cert['time_spec'], 'physical_time', physical, 'terminal:physical-time')):
        if endpoint is None: continue
        if endpoint['mode'] == 'fixed':
            v = endpoint['value']; require(type(v) is int and v >= 0, 'invalid fixed endpoint'); target = const(v)
        elif endpoint['mode'] == 'free': target = reg(endpoint.get('name', default), 'output')
        else: raise ValueError('invalid endpoint mode')
        square(label, minus(expr, target))
    expected = {'variables': variables, 'input_variables': inputs, 'output_variables': outputs,
                'squares': squares, 'products': products, 'steps': steps, 'loader': loader,
                'initial_N': start, 'final_N': prevN, 'physical_time': physical}
    for field, value in expected.items(): require(cert[field] == value, f'incorrect certificate structure: {field}')
    ledger = {'branch_count': B, 'source_horizon': h, 'core_variables': 2*B*h,
              'input_variables': len(inputs), 'output_variables': len(outputs),
              'loader_variables': loader.get('selector_count', 0), 'total_variables': len(variables),
              'core_squares': 3*h+1, 'loader_squares': loader.get('square_count', 0),
              'endpoint_squares': (cert['output_spec'] is not None)+(cert['time_spec'] is not None),
              'total_squares': len(squares), 'product_slots': B*h, 'maximum_degree': 2}
    require(cert['ledger'] == ledger, 'ledger mismatch')
    if 'expanded_polynomial' in cert:
        expanded = {}
        pairs = [(s['affine'], s['affine']) for s in squares]
        pairs += [(p['left'], p['right']) for p in products]
        for left, right in pairs:
            for x, a in left.items():
                for y, b in right.items():
                    key = tuple(sorted(v for v in (x, y) if v))
                    expanded[key] = expanded.get(key, 0)+a*b
        canonical = [{'monomial': list(k), 'coefficient': v}
                     for k, v in sorted(expanded.items()) if v]
        require(cert['expanded_polynomial'] == canonical, 'incorrect expanded polynomial')
    require(set(witness) == set(variables), 'witness variables missing or excessive')
    require(all(type(x) is int and x >= 0 for x in witness.values()), 'witness must be natural')
    residuals = [ev(s['affine'], witness)**2 for s in squares]
    residuals += [ev(p['left'], witness)*ev(p['right'], witness) for p in products]
    require(all(x >= 0 for x in residuals), 'nonnegative presentation violated')
    require(sum(residuals) == 0, 'polynomial is not zero')
    N, q, tick = ev(start, witness), cert['initial_state'], 0
    require(N >= 1, 'nonpositive starting N')
    trace = [{'step': 0, 'state': q, 'N': N, 'microtime': 0}]
    for t, local in enumerate(steps):
        require(q != halt, 'continuation after committed halt')
        chosen = [j for j,l in enumerate(local) if witness[l['e']] == 1]
        require(len(chosen) == 1, 'selector is not one-hot')
        j = chosen[0]; b = branches[j]; row = local[j]
        require(all(witness[l['e']] == witness[l['u']] == 0 for k,l in enumerate(local) if k != j),
                'inactive branch witness not zero')
        require(q == b['source'], 'source control mismatch')
        p, op = b['prime'], b['operation']
        before = N
        if op == 'inc': N *= p; dt = 108*before+96*N+8
        elif op == 'dec':
            require(N % p == 0, 'invalid decrement'); N //= p; dt = 96*before+108*N+8
        elif op == 'positive': require(N % p == 0, 'invalid positive test'); dt = 192*N+8
        elif op == 'zero': require(N % p == b['residue'], 'invalid zero-test residue'); dt = 192*N+8
        else: dt = 192*N+8
        require(ev(row['old'], witness) == before and ev(row['new'], witness) == N
                and ev(row['ticks'], witness) == dt, 'branch value or clock mismatch')
        q, tick = b['target'], tick+dt
        trace.append({'step': t+1, 'state': q, 'N': N, 'microtime': clock_scale*tick, 'branch': j})
    require(q == halt, 'not a committed halt')
    return {'status': 'passed', 'source_trace': trace, 'final_N': N,
            'physical_time': clock_scale*tick, 'ledger': ledger}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('certificate'); p.add_argument('witness'); p.add_argument('--receipt')
    a = p.parse_args()
    result = check(json.loads(Path(a.certificate).read_text()), json.loads(Path(a.witness).read_text()))
    text = json.dumps(result, indent=2)+'\n'
    if a.receipt: Path(a.receipt).write_text(text)
    else: print(text, end='')

if __name__ == '__main__': main()
