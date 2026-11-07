"""Emit the Lean let-chain of package 55's 14-positive, 79-operation circuit.

Usage: py -I -X utf8 -S -B generate_p55.py [--check LEAN_FILE]

The equation is `55-congruence-norms/fourteen/polynomial.json`, degree 52, at
the wang943-mixed-121x8801 ports. Inputs: J F alpha z f i T s w tau eta zeta e
gamma. The four ports are the `let`-bound `.constant (p k)` leaves beta, K0,
MC, MF. Gates keep their JSON names. With --check, compare against the block
between the markers in LEAN_FILE. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '55-congruence-norms',
                      'fourteen', 'polynomial.json')
PIN = 'd888c3f13c404b63c23257dce5ca67ab2e2caa699bceb810a5520517b0bd02db'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
assert inputs == ['J', 'F', 'alpha', 'z', 'f', 'i', 'T', 's', 'w', 'tau', 'eta', 'zeta', 'e',
                  'gamma']
assert d['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert d['operations'] == len(d['source']) == 79 and d['output'] == 'polynomial'
assert d['exact_degree'] == 52

known = set(inputs) | {'beta', 'K0', 'MC', 'MF'}
lines = []
for name, op, a, b in d['source']:
    assert op in '+-*' and name not in known, (name, op)
    ops = []
    for x in (a, b):
        if isinstance(x, int):
            assert x >= 0; ops.append(str(x))
        else:
            assert x in known, x; ops.append(x)
    lines.append(f'  let {name} := {ops[0]} {op} {ops[1]}')
    known.add(name)
block = '\n'.join(lines)

if len(sys.argv) == 3 and sys.argv[1] == '--check':
    text = open(sys.argv[2], encoding='utf-8').read()
    start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
    end = text.index('  -- END LITERAL GRAPH')
    if text[start:end].rstrip('\n') != block:
        sys.exit('Lean graph block differs from the JSON circuit')
    print(f'ok: 79 gates match; source sha256 {digest}')
else:
    print(block)
