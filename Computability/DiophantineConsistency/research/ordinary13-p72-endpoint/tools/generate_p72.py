"""Emit the Lean let-chain of package 72's 13-positive, 98-operation circuit P13.

Usage: py -I -X utf8 -S -B generate_p72.py [--check LEAN_FILE]

Inputs J-free: F alpha C f0 i T X Y r eta zeta u gamma. The four ports are
`.constant (p k)`; the six derived fixed leaves (B, b, b2, L, Kfinal,
four_beta) are `.constant` of their JSON recipes evaluated on `p 0`, so they
cost no operations, as in the package's count. With --check, compare against
the block between the markers in LEAN_FILE. The JSON input is pinned by SHA-256.
"""
import hashlib, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..', '..'))
SOURCE = os.path.join(ROOT, 'con-zfc-diophantine-forms', '72-congruence-sextic',
                      'positive13', 'p13_degree28.json')
PIN = '1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49'

raw = open(SOURCE, 'rb').read()
digest = hashlib.sha256(raw).hexdigest()
if digest != PIN:
    sys.exit(f'source hash {digest} differs from pin {PIN}')
d = json.loads(raw.decode('utf-8'))
inputs = d['witnesses']
assert inputs == ['F', 'alpha', 'C', 'f0', 'i', 'T', 'X', 'Y', 'r', 'eta', 'zeta', 'u', 'gamma']
assert d['fixed_ports'] == ['beta', 'K0', 'MC', 'MF']
assert d['operations'] == len(d['source']) == 98 and d['output'] == 'g97'
assert d['residuals'] == ['A0', 'A1', 'Aa', 'As']
port = {'beta': '(p 0)', 'K0': '(p 1)', 'MC': '(p 2)', 'MF': '(p 3)'}

def recipe(e):
    if isinstance(e, int):
        return str(e)
    if isinstance(e, str):
        return port[e] if e in port else derived_int[e]
    op, a, b = e
    assert op in '+*'
    return f'({recipe(a)} {op} {recipe(b)})'

derived_int = {}
for name in ['B', 'b', 'b2', 'L', 'Kfinal', 'four_beta']:
    derived_int[name] = recipe(d['derived_fixed_leaves'][name])
assert set(d['derived_fixed_leaves']) == set(derived_int)

lines = [f'  let {n} : Expr (Fin 13) := .constant {derived_int[n]}' for n in
         ['B', 'b', 'b2', 'L', 'Kfinal', 'four_beta']]
known = set(inputs) | set(port) | set(derived_int)
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
    print(f'ok: 98 gates and 6 derived leaves match; source sha256 {digest}')
else:
    print(block)
