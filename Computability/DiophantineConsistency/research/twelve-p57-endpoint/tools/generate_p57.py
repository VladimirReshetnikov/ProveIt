"""Emit the Lean let-chain of package 57's 12-positive, 89-operation circuit.

Usage: py -I -X utf8 -S -B generate_p57.py [--check LEAN_FILE]

Inputs: J F alpha z i T s w eta zeta y t. The four ports are the
`let`-bound `.constant (p k)` leaves beta, K0, MC, MF. Gates keep their JSON
names. With --check, compare against the block between the markers in
LEAN_FILE. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '57-separated-degrees',
                      'low_degree', 'twelve_positive_degree258.json')
PIN = '9e9db19a68ddb52e0b2c75accb68b7d082a78d338fe03239f2ce73dcf7829188'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
assert inputs == ['J', 'F', 'alpha', 'z', 'i', 'T', 's', 'w', 'eta', 'zeta', 'y',
                  't']
assert d['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert d['operations'] == len(d['source']) == 89 and d['output'] == 'out'

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
    print(f'ok: 89 gates match; source sha256 {digest}')
else:
    print(block)
