#!/usr/bin/env python3
"""Independently inspect the sign25-to-sign24 external AST reduction."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
old_path = root / 'research/nine-sharing-sign25-octic-ell-candidate/seed.json'
new_path = root / 'research/nine-sharing-sign24-octic-q3-candidate/seed.json'
digest = lambda data: hashlib.sha256(data).hexdigest()
assert digest(old_path.read_bytes()) == 'c95637ae24a57dba0ae1113a8256ed6f12d33f416f035f9cd4f92cffdbf59fc8'
assert digest(new_path.read_bytes()) == '24a6dcf05b96112cfa332aafe4790a367c44b9a0cc033a74197f92d3520ab865'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 25 and new['witness_count'] == 24
assert new['total_coordinates'] == 25 and new['distinguished_input_coordinate'] == 0
assert new['fixed_ports'] == old['fixed_ports'] and new['coefficient_binding'] == old['coefficient_binding']
old_rows = old['residuals']
new_rows = new['residuals']
removed, = [r for r in old_rows if r['gate'] == 'q3']
assert removed['kind'] == 'positive'
factor = ['add', ['mul', ['port', 'beta'], ['add', ['var', 1], ['num', 1]]], ['num', 1]]
cube = ['mul', ['mul', factor, factor], factor]
assert removed['expr'] == ['sub', ['var', 15], cube]
assert new['lift_expression'] == cube

def substitute(tree):
    op, *args = tree
    if op == 'var':
        i, = args
        assert 0 <= i <= 25
        return cube if i == 15 else ['var', i - (i > 15)]
    if op in ('port', 'num'):
        return tree
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    return [op, *(substitute(arg) for arg in args)]

retained = [r for r in old_rows if r['gate'] != 'q3']
assert len(retained) == len(new_rows) == 15
for before, after in zip(retained, new_rows):
    assert before.keys() == after.keys()
    for key in before:
        assert after[key] == (substitute(before[key]) if key == 'expr' else before[key])

def degree(tree, selected=None):
    op, *args = tree
    if op == 'var':
        assert 0 <= args[0] < 25
        return int(selected is None or args[0] in selected)
    if op in ('num', 'port'):
        return 0
    a, b = (degree(x, selected) for x in args)
    return a + b if op == 'mul' else max(a, b)

assert all(degree(r['expr']) <= 4 for r in new_rows)
assert all(degree(r['expr'], {16, 17}) <= 2 for r in new_rows if r['gate'] != 'N0')

# Calculate N0 as a univariate integer polynomial, not by interpolation.
def add(a, b, sign=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + sign * v
    return {k: v for k, v in out.items() if v}

def polynomial(tree):
    op, *args = tree
    if op == 'num': return {0: args[0]} if args[0] else {}
    if op == 'var': return {1: 1} if args[0] in (16, 17) else {}
    assert op != 'port', 'N0 specialization unexpectedly depends on a port'
    a, b = (polynomial(x) for x in args)
    if op == 'add': return add(a, b)
    if op == 'sub': return add(a, b, -1)
    assert op == 'mul'
    result = {}
    for i, x in a.items():
        for j, y in b.items():
            result[i+j] = result.get(i+j, 0) + x*y
    return {k: v for k, v in result.items() if v}

n0, = [r for r in new_rows if r['gate'] == 'N0']
assert polynomial(n0['expr']) == {4: -1, 2: -2, 0: -1}

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
for port, info in binding['ports'].items():
    path = new_path.parent / binding['path'] / info['file']
    data = path.read_bytes()
    raw = gzip.decompress(data)
    assert digest(data) == info['gzip_sha256'] and digest(raw) == info['raw_sha256']
    assert len(raw) == info['raw_bytes']
    if port == 'beta': assert any(raw)
for path_key, hash_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert digest((new_path.parent / binding[path_key]).read_bytes()) == binding[hash_key]

print(json.dumps({'status': 'PASS_EXTERNAL_AST_AUDIT', 'retained_residuals': 15,
                  'N0_t_polynomial': '-t^4-2*t^2-1', 'sum_of_squares_degree': 8,
                  'claim': 'external AST only; no Lean bridge, endpoint, or PDF binding'}, sort_keys=True))
