"""Fresh bounded structural/degree checks of inert supplied JSON; no source imports."""
import collections
import hashlib
import json
from pathlib import Path

ROOT = Path('/tmp/sandpiles_0d7f51c44')
PINS = [
    '2e2403097ba0fb65bad349222246157bccad4ac59e99d594b48fa7a678a93723',
    '352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504',
    '7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6',
    '8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759',
]

def need(condition, message):
    if not condition:
        raise ValueError(message)

def poly(op, a, b):
    if op == '*':
        c = [0] * (len(a) + len(b) - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                c[i+j] += x*y
    else:
        c = [0] * max(len(a), len(b))
        for i, x in enumerate(a): c[i] += x
        for i, y in enumerate(b): c[i] += y if op == '+' else -y
    while len(c) > 1 and c[-1] == 0: c.pop()
    return c

def check(index):
    raw = (ROOT / f'{index}_DAG.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == PINS[index], 'source pin')
    d = json.loads(raw)
    gates, witnesses, equations = d['gates'], d['witnesses'], d['equalities']
    need(len(witnesses) == len(set(witnesses)), 'unique witnesses')
    prefix = 'input' if index == 0 else 'descriptor'
    line = {prefix+'.'+s for s in ('p','q','r','d','e','f')} | {'box.tx','box.ty','box.tz'}
    need(line <= set(witnesses), 'actual specialization ports')
    vals = {'witness:'+w: ([0,1] if w in line else [0]) for w in witnesses}
    degrees = {'witness:'+w: 1 for w in witnesses}
    vals['input:'+d['input']] = [0]
    degrees['input:'+d['input']] = 1
    refs = {}
    for j, row in enumerate(gates):
        need(len(row) == 3 and row[0] in '+-*', 'binary row schema')
        op, a, b = row
        for x in (a,b):
            if x.startswith('constant:'):
                vals[x] = [int(x.split(':',1)[1])]
                degrees[x] = 0
            need(x in vals, 'closure/topological order')
        name = f'gate:{j}'
        vals[name] = poly(op, vals[a], vals[b])
        degrees[name] = degrees[a]+degrees[b] if op == '*' else max(degrees[a],degrees[b])
        refs[name] = (a,b)
    live = set(); stack = [d['output']]
    while stack:
        x = stack.pop()
        if x in live: continue
        live.add(x); stack.extend(refs.get(x, ()))
    need(set(refs) <= live, 'all gates live')
    need({'witness:'+w for w in witnesses} <= live, 'all witnesses live')
    need('input:'+d['input'] in live, 'input live')
    body = len(gates) - (3*len(equations)-1)
    need(d.get('body_gate_count',body) == body, 'body count')
    expected = []; squares = []
    for a,b,label in equations:
        need(a in degrees and b in degrees, 'equation refs')
        rid = 'gate:'+str(body+len(expected)); expected.append(['-',a,b])
        sid = 'gate:'+str(body+len(expected)); expected.append(['*',rid,rid]); squares.append(sid)
    total = squares[0]
    for s in squares[1:]:
        expected.append(['+',total,s]); total = 'gate:'+str(body+len(expected)-1)
    need(gates[body:] == expected and d['output'] == total, 'literal whole SOS suffix')
    need(degrees[total] == 18, 'syntactic degree upper bound')
    need(len(vals[total])-1 == 18 and vals[total][-1] == 48, 'exact degree line')
    return {'report':[50,52,53,54][index], 'dag_sha256':PINS[index],
            'gates':len(gates), 'operations':dict(collections.Counter(g[0] for g in gates)),
            'witnesses':len(witnesses), 'residuals':len(equations), 'body_gates':body,
            'macro_kinds':dict(collections.Counter(m['kind'] for m in d['macros'])),
            'closure_and_all_gates_witnesses_input_live':True, 'literal_sos_suffix':True,
            'degree_upper':18, 'specialization_ports':sorted(line),
            'specialization_coefficients':vals[total], 'degree':18,'leading_coefficient':48}

if __name__ == '__main__':
    print(json.dumps({'scope':'syntax, count, liveness, literal SOS and one exact degree line only; not residual-to-macro reconstruction or all-input semantics',
                      'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      'reports':[check(i) for i in range(4)]},indent=2))
