#!/usr/bin/env python3
"""Eliminate three positive cuts, retaining a reproducible external AST."""
import copy
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'nine-sharing-sign31-sextic-candidate' / 'seed.json'
raw = SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '827740a7f65961bd1a04ae424f4c8873a636285d2b1410bb72d0bee7e3e9e6c1'
old = json.loads(raw)
assert old['witness_count'] == 31 and len(old['residuals']) == 22
rows = copy.deepcopy(old['residuals'])
steps = []

def transform(t, index, replacement):
    op = t[0]
    if op == 'var':
        if t[1] == index:
            return transform(copy.deepcopy(replacement), index, replacement)
        return ['var', t[1] - 1 if t[1] > index else t[1]]
    if op in ('num', 'port'):
        return copy.deepcopy(t)
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    return [op, transform(t[1], index, replacement), transform(t[2], index, replacement)]

def contains(t, index):
    if t[0] == 'var': return t[1] == index
    if t[0] in ('num', 'port'): return False
    return contains(t[1], index) or contains(t[2], index)

for gate in ('X', 'c2', 'normalized_S2'):
    row, = (r for r in rows if r['gate'] == gate)
    expr = row['expr']
    assert row['kind'] == 'positive' and expr[0] == 'sub' and expr[1][0] == 'var'
    index, replacement = expr[1][1], expr[2]
    assert not contains(replacement, index)
    steps.append({'gate': gate, 'old_coordinate_at_step': index, 'replacement_before_drop': copy.deepcopy(replacement)})
    rows = [dict(r, expr=transform(r['expr'], index, replacement)) for r in rows if r['gate'] != gate]

assert len(rows) == 19
out = {
    'schema': 'sharing-sextic-substituted-q2-f2-X-c2-S2-v1',
    'source': '../nine-sharing-sign31-sextic-candidate/seed.json',
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'distinguished_input_coordinate': 0,
    'witness_count': 28,
    'total_coordinates': 29,
    'elimination_steps': steps,
    'fixed_ports': old['fixed_ports'],
    'coefficient_binding': old['coefficient_binding'],
    'residuals': rows,
    'output': 'sum of squares of the 19 displayed residuals',
    'status': 'external source candidate; no Lean equivalence or endpoint',
}
encoded = (json.dumps(out, indent=2, sort_keys=True) + '\n').encode()
target = HERE / 'seed.json'
if sys.argv[1:] == ['--write']:
    with target.open('xb') as f: f.write(encoded)
elif sys.argv[1:] == ['--check']:
    assert target.read_bytes() == encoded
    print(json.dumps({'status': 'PASS_REPRODUCIBLE_AST_ONLY', 'sha256': hashlib.sha256(encoded).hexdigest()}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
