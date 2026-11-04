"""Emit the Lean let-chain of package 115's 13-positive, 87-operation circuit.

Usage: py -I -X utf8 -S -B generate_graph.py [--check LEAN_FILE]

Without arguments, print the block. With --check, compare it against the
text between "-- BEGIN LITERAL GRAPH" and "-- END LITERAL GRAPH" in
LEAN_FILE and exit 1 on any difference. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '115-synchronized-exponents',
                      'supplement', 'circuits', 'positive13_87_degree51.json')
PIN = '24b9120cc07693ba3fab0bff254c071fae800d14415850c3411651c026e28f0c'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if PIN != '__PIN__' and digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
consts = d['fixed_numerals']
assert inputs == ['J', 'F', 'alpha', 'f', 'i', 'T', 'X', 'Y', 'r', 'eta', 'zeta', 'u', 'gamma']
assert consts == ['beta', 'K0', 'MC', 'MF']
assert d['operations'] == len(d['source']) == 87 and d['output'] == 'P13'
assert d['residuals'] == ['A0', 'A1', 'Fa', 'Fs']

def operand(x, known):
    if isinstance(x, int):
        assert x >= 0
        return str(x)
    assert x in known, x
    return x

lines = []
known = set(inputs) | set(consts)
for name, op, a, b in d['source']:
    assert op in '+-*' and name not in known, (name, op)
    lines.append(f'  let {name} := {operand(a, known)} {op} {operand(b, known)}')
    known.add(name)
block = '\n'.join(lines)

if len(sys.argv) == 3 and sys.argv[1] == '--check':
    text = open(sys.argv[2], encoding='utf-8').read()
    start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
    end = text.index('  -- END LITERAL GRAPH')
    got = text[start:end].rstrip('\n')
    if got != block:
        sys.exit('Lean graph block differs from the JSON circuit')
    print(f'ok: 87 gates match; source sha256 {digest}')
else:
    print(block)
    print(f'-- source sha256 {digest}', file=sys.stderr)
