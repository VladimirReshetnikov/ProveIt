"""Emit the Lean let-chain of package 64's 14-positive, 83-operation circuit.

Usage: py -I -X utf8 -S -B generate_p64.py [--check LEAN_FILE]

Inputs: J F alpha z f i T Y w rho eta zeta e gamma. The four ports are the
`let`-bound `.constant (p k)` leaves beta, K0, MC, MF. Gates keep their JSON
names. With --check, compare against the block between the markers in
LEAN_FILE. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '64-structural-reductions',
                      'positive14', 'polynomial.json')
PIN = 'b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
assert inputs == ['J', 'F', 'alpha', 'z', 'f', 'i', 'T', 'Y', 'w', 'rho', 'eta', 'zeta', 'e',
                  'gamma']
assert d['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert d['operations'] == len(d['source']) == 83 and d['output'] == 'polynomial'

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
    print(f'ok: 83 gates match; source sha256 {digest}')
else:
    print(block)
