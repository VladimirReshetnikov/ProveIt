#!/usr/bin/env python3
"""Independent structural and exact-degree audit of the external Delta cut."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
old_path = root / 'research/nine-sharing-sign22-dodecic-ky-candidate/seed.json'
new_path = root / 'research/nine-sharing-sign21-degree14-s-candidate/seed.json'
digest = lambda data: hashlib.sha256(data).hexdigest()
assert digest(old_path.read_bytes()) == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
assert digest(new_path.read_bytes()) == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 22 and new['witness_count'] == 21
assert new['total_coordinates'] == 22 and new['distinguished_input_coordinate'] == 0
assert new['fixed_ports'] == old['fixed_ports'] and new['coefficient_binding'] == old['coefficient_binding']
removed, = [r for r in old['residuals'] if r['gate'] == 'normalized_S']
assert removed['kind'] == 'positive'
replacement = ['mul', ['add', ['var', 6], ['num', 1]], ['mul', ['var', 17], ['add', ['var', 17], ['num', 2]]]]
assert removed['expr'] == ['sub', ['var', 21], replacement]
assert new['lift_expression'] == replacement

def substitute(tree):
    op, *args = tree
    if op == 'var':
        i, = args
        assert 0 <= i <= 22
        return replacement if i == 21 else ['var', i - (i > 21)]
    if op in ('port', 'num'): return tree
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    return [op, *(substitute(arg) for arg in args)]

retained = [r for r in old['residuals'] if r['gate'] != 'normalized_S']
assert len(retained) == len(new['residuals']) == 12
for before, after in zip(retained, new['residuals']):
    assert before.keys() == after.keys()
    for key in before:
        assert after[key] == (substitute(before[key]) if key == 'expr' else before[key])

def degree(tree):
    op, *args = tree
    if op == 'var':
        assert 0 <= args[0] < 22
        return 1
    if op in ('num', 'port'): return 0
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    a, b = (degree(x) for x in args)
    return a + b if op == 'mul' else max(a, b)
assert all(degree(r['expr']) <= 7 for r in new['residuals'])

# Calculate N0 exactly as a polynomial in t when v6=v17=v21=t, input one, and others vanish.
def add(a, b, sign=1):
    out = dict(a)
    for k, value in b.items(): out[k] = out.get(k, 0) + sign * value
    return {k: value for k, value in out.items() if value}

def polynomial(tree):
    op, *args = tree
    if op == 'num': return {0: args[0]} if args[0] else {}
    if op == 'var': return {1: 1} if args[0] in (6, 17, 21) else ({0: 1} if args[0] == 0 else {})
    assert op != 'port', 'N0 specialization unexpectedly depends on a port'
    a, b = (polynomial(x) for x in args)
    if op == 'add': return add(a, b)
    if op == 'sub': return add(a, b, -1)
    assert op == 'mul'
    out = {}
    for i, x in a.items():
        for j, y in b.items(): out[i+j] = out.get(i+j, 0) + x*y
    return {k: value for k, value in out.items() if value}
n0, = [r for r in new['residuals'] if r['gate'] == 'Na']
assert polynomial(n0['expr']) == {7: -1, 6: -6, 5: -13, 4: -12, 3: -4}

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
for info in binding['ports'].values():
    data = (new_path.parent / binding['path'] / info['file']).read_bytes()
    raw = gzip.decompress(data)
    assert digest(data) == info['gzip_sha256'] and digest(raw) == info['raw_sha256']
    assert len(raw) == info['raw_bytes']
for path_key, hash_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert digest((new_path.parent / binding[path_key]).read_bytes()) == binding[hash_key]
print(json.dumps({'status': 'PASS_EXTERNAL_AST_AUDIT', 'retained_residuals': 12,
                  'Na_t_polynomial': '-t^7-6*t^6-13*t^5-12*t^4-4*t^3', 'sum_of_squares_degree': 14,
                  'claim': 'external AST only; no Lean bridge, endpoint, or PDF binding'}, sort_keys=True))
