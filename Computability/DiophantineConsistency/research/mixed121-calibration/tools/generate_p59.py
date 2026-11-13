"""Emit the Lean let-chain of package 59's 14-positive, 79-operation circuit.

Usage: py -I -X utf8 -S -B generate_p59.py [--check LEAN_FILE]

The equation is `59-degree-separated/short/circuits/p79_d52_14positive.json`,
degree 52 (per the package's AUDIT.json), at the wang943-mixed-121x8801 ports
(its COEFFICIENT_BINDING.json pins the same four payload hashes as package 55).
Inputs: J F alpha z f i T s w tau eta zeta u gamma. The four ports are the `let`-bound `.constant (p k)` leaves beta, K0,
MC, MF. Gates keep their JSON names. With --check, compare against the block
between the markers in LEAN_FILE. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
PKG = os.path.join(ROOT, 'con-zfc-diophantine-forms', '59-degree-separated', 'short')
SOURCE = os.path.join(PKG, 'circuits', 'p79_d52_14positive.json')
PIN = 'b2d565740add0deec15905a99ca019f048e3f116c0d68b08e25bb1057fb8f584'
PORTS55 = os.path.join(ROOT, 'con-zfc-diophantine-forms', '55-congruence-norms', 'fourteen',
                       'coefficients', 'ports.json')

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
assert inputs == ['J', 'F', 'alpha', 'z', 'f', 'i', 'T', 's', 'w', 'tau', 'eta', 'zeta', 'u',
                  'gamma']
assert d['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF']
assert len(d['source']) == 79 and d['output'] == 'polynomial'
audit = json.load(open(os.path.join(PKG, 'AUDIT.json'), encoding='utf-8'))
entry = [c for c in audit['circuits'] if c['name'] == 'p79_d52_14positive']
assert len(entry) == 1 and entry[0]['sha256'] == PIN and entry[0]['exact_degree'] == 52
assert entry[0]['operations'] == 79 and entry[0]['variables'] == 14
# The coefficient binding pins exactly package 55's four payload hashes.
import re
pins59 = re.findall(r'"sha256": *"([0-9a-f]{64})"',
                    open(os.path.join(PKG, 'COEFFICIENT_BINDING.json'), encoding='utf-8').read())[:4]
pins55 = re.findall(r'"sha256": *"([0-9a-f]{64})"', open(PORTS55, encoding='utf-8').read())[:4]
assert pins59 == pins55 and len(pins55) == 4, (pins59, pins55)

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
    print(f'ok: 79 gates match; source sha256 {digest}; ports = package 55 ports')
else:
    print(block)
