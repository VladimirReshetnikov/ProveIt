"""Emit the Lean let-chain of package 65's 14-positive, 92-operation circuit.

Usage: py -I -X utf8 -S -B generate_p65.py [--check LEAN_FILE]

Inputs: j F alpha z f i T x Y r eta zeta u gamma. The four ports are
`.constant (p k)`. Gates keep their JSON ids `v0`..`v91`, except that a gate
named in the JSON `registers` map takes that register name. With --check,
compare against the block between the markers in LEAN_FILE. The JSON input is
pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '65-shared-taps', 'pell',
                      'circuits', 'p14_degree26.json')
PIN = '0ceb30c9ba9b6a3387ac55d6591d56f5e9746626aaec6fecd2293402f233b137'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['variables']
assert inputs == ['j', 'F', 'alpha', 'z', 'f', 'i', 'T', 'x', 'Y', 'r', 'eta', 'zeta', 'u',
                  'gamma']
assert d['fixed_ports'] == ['beta', 'K0', 'MC', 'MF']
assert len(d['gates']) == 92 and d['output'] == 'v91'
port = {'beta': 'beta', 'K0': 'K0', 'MC': 'MC', 'MF': 'MF'}
rename = {g: r for r, g in d['registers'].items() if g.startswith('v')}
assert len(rename) == len(set(rename.values()))
sym = {'add': '+', 'sub': '-', 'mul': '*'}

known = set(inputs) | set(port)
lines = []
for n, g in enumerate(d['gates']):
    assert g['id'] == f'v{n}' and g['op'] in sym and len(g['args']) == 2
    ops = []
    for x in g['args']:
        if isinstance(x, int):
            assert x >= 0; ops.append(str(x))
        else:
            x = rename.get(x, x)
            assert x in known, x; ops.append(x)
    name = rename.get(g['id'], g['id'])
    assert name not in known and name not in ('P26',), name
    lines.append(f'  let {name} := {ops[0]} {sym[g["op"]]} {ops[1]}')
    known.add(name)
lines.append(f'  let P26 := {rename.get("v91", "v91")}')
block = '\n'.join(lines)

if len(sys.argv) == 3 and sys.argv[1] == '--check':
    text = open(sys.argv[2], encoding='utf-8').read()
    start = text.index('-- BEGIN LITERAL GRAPH\n') + len('-- BEGIN LITERAL GRAPH\n')
    end = text.index('  -- END LITERAL GRAPH')
    if text[start:end].rstrip('\n') != block:
        sys.exit('Lean graph block differs from the JSON circuit')
    print(f'ok: 92 gates match; source sha256 {digest}')
else:
    print(block)
