#!/usr/bin/env python3
"""Independent structural and exact-degree audit of the external Delta cut."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
old_path = root / 'research/nine-sharing-sign24-octic-q3-candidate/seed.json'
new_path = root / 'research/nine-sharing-sign23-octic-delta-candidate/seed.json'
digest = lambda data: hashlib.sha256(data).hexdigest()
assert digest(old_path.read_bytes()) == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
assert digest(new_path.read_bytes()) == 'ee6079ea26dd120fab39789f83034947c18e0c8806945a1fc75fca62e1c65d41'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 24 and new['witness_count'] == 23
assert new['total_coordinates'] == 24 and new['distinguished_input_coordinate'] == 0
assert new['fixed_ports'] == old['fixed_ports'] and new['coefficient_binding'] == old['coefficient_binding']
removed, = [r for r in old['residuals'] if r['gate'] == 'Delta']
assert removed['kind'] == 'positive'
v = ['add', ['var', 16], ['var', 15]]
replacement = ['add', ['mul', v, v], ['add', ['mul', ['num', 4], v], ['num', 3]]]
assert removed['expr'] == ['sub', ['var', 18], replacement]
assert new['lift_expression'] == replacement

def substitute(tree):
    op, *args = tree
    if op == 'var':
        i, = args
        assert 0 <= i <= 24
        return replacement if i == 18 else ['var', i - (i > 18)]
    if op in ('port', 'num'): return tree
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    return [op, *(substitute(arg) for arg in args)]

retained = [r for r in old['residuals'] if r['gate'] != 'Delta']
assert len(retained) == len(new['residuals']) == 14
for before, after in zip(retained, new['residuals']):
    assert before.keys() == after.keys()
    for key in before:
        assert after[key] == (substitute(before[key]) if key == 'expr' else before[key])

def degree(tree):
    op, *args = tree
    if op == 'var':
        assert 0 <= args[0] < 24
        return 1
    if op in ('num', 'port'): return 0
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    a, b = (degree(x) for x in args)
    return a + b if op == 'mul' else max(a, b)
assert all(degree(r['expr']) <= 4 for r in new['residuals'])

# Calculate N0 exactly as a polynomial in t when v16=v17=t and others vanish.
def add(a, b, sign=1):
    out = dict(a)
    for k, value in b.items(): out[k] = out.get(k, 0) + sign * value
    return {k: value for k, value in out.items() if value}

def polynomial(tree):
    op, *args = tree
    if op == 'num': return {0: args[0]} if args[0] else {}
    if op == 'var': return {1: 1} if args[0] in (16, 17) else {}
    assert op != 'port', 'N0 specialization unexpectedly depends on a port'
    a, b = (polynomial(x) for x in args)
    if op == 'add': return add(a, b)
    if op == 'sub': return add(a, b, -1)
    assert op == 'mul'
    out = {}
    for i, x in a.items():
        for j, y in b.items(): out[i+j] = out.get(i+j, 0) + x*y
    return {k: value for k, value in out.items() if value}
n0, = [r for r in new['residuals'] if r['gate'] == 'N0']
assert polynomial(n0['expr']) == {4: -1, 2: -2, 0: -1}

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
for info in binding['ports'].values():
    data = (new_path.parent / binding['path'] / info['file']).read_bytes()
    raw = gzip.decompress(data)
    assert digest(data) == info['gzip_sha256'] and digest(raw) == info['raw_sha256']
    assert len(raw) == info['raw_bytes']
for path_key, hash_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert digest((new_path.parent / binding[path_key]).read_bytes()) == binding[hash_key]
print(json.dumps({'status': 'PASS_EXTERNAL_AST_AUDIT', 'retained_residuals': 14,
                  'N0_t_polynomial': '-t^4-2*t^2-1', 'sum_of_squares_degree': 8,
                  'claim': 'external AST only; no Lean bridge, endpoint, or PDF binding'}, sort_keys=True))
