#!/usr/bin/env python3
"""Reproducibly eliminate the f² coordinate from the 32-witness AST."""
import copy
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / 'nine-sharing-sign32-sextic-candidate-v2' / 'seed.json'
raw = SOURCE.read_bytes()
assert hashlib.sha256(raw).hexdigest() == 'f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab'
old = json.loads(raw)
assert old['witness_count'] == 32 and old['total_coordinates'] == 33
assert len(old['residuals']) == 23
row, = (r for r in old['residuals'] if r['gate'] == 'f2')
assert row['kind'] == 'positive' and row['expr'][0:2] == ['sub', ['var', 27]]
replacement = row['expr'][2]
assert replacement == ['mul', ['add', ['var', 5], ['num', 1]], ['add', ['var', 5], ['num', 1]]]

def transform(t):
    op = t[0]
    if op == 'var':
        i = t[1]
        if i == 27:
            return copy.deepcopy(replacement)
        return ['var', i - 1 if i > 27 else i]
    if op in ('num', 'port'):
        return copy.deepcopy(t)
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    return [op, transform(t[1]), transform(t[2])]

rows = []
for r in old['residuals']:
    if r['gate'] != 'f2':
        new = copy.deepcopy(r)
        new['expr'] = transform(r['expr'])
        rows.append(new)
assert len(rows) == 22
out = {
    'schema': 'sharing-sextic-substituted-q2-f2-v1',
    'source': '../nine-sharing-sign32-sextic-candidate-v2/seed.json',
    'source_sha256': hashlib.sha256(raw).hexdigest(),
    'distinguished_input_coordinate': 0,
    'witness_count': 31,
    'total_coordinates': 32,
    'coordinate_mapping': 'old 0..26 unchanged; old 27 is f^2; old 28..32 map to new 27..31',
    'substituted_f2': replacement,
    'fixed_ports': old['fixed_ports'],
    'coefficient_binding': old['coefficient_binding'],
    'residuals': rows,
    'output': 'sum of squares of the 22 displayed residuals',
    'status': 'external source candidate; no Lean equivalence or endpoint',
}
encoded = (json.dumps(out, indent=2, sort_keys=True) + '\n').encode()
target = HERE / 'seed.json'
if sys.argv[1:] == ['--write']:
    with target.open('xb') as f:
        f.write(encoded)
elif sys.argv[1:] == ['--check']:
    assert target.read_bytes() == encoded
    print(json.dumps({'status': 'PASS_REPRODUCIBLE_AST_ONLY', 'sha256': hashlib.sha256(encoded).hexdigest()}, sort_keys=True))
else:
    raise SystemExit('expected --write or --check')
