#!/usr/bin/env python3
"""Independent structural and exact-degree audit of the external Delta cut."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site
root = Path(__file__).resolve().parents[2]
old_path = root / 'research/nine-sharing-sign21-degree14-s-candidate/seed.json'
new_path = root / 'research/nine-sharing-sign20-degree20-e-candidate/seed.json'
digest = lambda data: hashlib.sha256(data).hexdigest()
assert digest(old_path.read_bytes()) == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
assert digest(new_path.read_bytes()) == '2593aca2ac701ff9312fe5aff1719bbf4fd29a97e2c3e14642bf137d6ef8bf7d'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 21 and new['witness_count'] == 20
assert new['total_coordinates'] == 21 and new['distinguished_input_coordinate'] == 0
assert new['fixed_ports'] == old['fixed_ports'] and new['coefficient_binding'] == old['coefficient_binding']
removed, = [r for r in old['residuals'] if r['gate'] == 'E']
assert removed['kind'] == 'positive'
replacement = ['mul', ['mul', ['add', ['var', 9], ['num', 1]], ['add', ['mul', ['port', 'beta'], ['add', ['var', 1], ['num', 1]]], ['num', 1]]], ['var', 15]]
assert removed['expr'] == ['sub', ['var', 16], replacement]
assert new['lift_expression'] == replacement

def substitute(tree):
    op, *args = tree
    if op == 'var':
        i, = args
        assert 0 <= i <= 21
        return replacement if i == 16 else ['var', i - (i > 16)]
    if op in ('port', 'num'): return tree
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    return [op, *(substitute(arg) for arg in args)]

retained = [r for r in old['residuals'] if r['gate'] != 'E']
assert len(retained) == len(new['residuals']) == 11
for before, after in zip(retained, new['residuals']):
    assert before.keys() == after.keys()
    for key in before:
        assert after[key] == (substitute(before[key]) if key == 'expr' else before[key])

def degree(tree):
    op, *args = tree
    if op == 'var':
        assert 0 <= args[0] < 21
        return 1
    if op in ('num', 'port'): return 0
    assert op in ('add', 'sub', 'mul') and len(args) == 2
    a, b = (degree(x) for x in args)
    return a + b if op == 'mul' else max(a, b)
assert all(degree(r['expr']) <= 10 for r in new['residuals'])

# Specialize input to 1, v1=v9=v11=v15=t, other coordinates to zero;
# represent coefficients in Z[t,beta] exactly.
def plus(a,b,sign=1):
    out=dict(a)
    for k,v in b.items(): out[k]=out.get(k,0)+sign*v
    return {k:v for k,v in out.items() if v}
def poly(tree):
    op,*args=tree
    if op=='num': return {(0,0):args[0]} if args[0] else {}
    if op=='port':
        assert args[0]=='beta'
        return {(0,1):1}
    if op=='var': return {(1,0):1} if args[0] in (1,9,11,15) else ({(0,0):1} if args[0]==0 else {})
    a,b=map(poly,args)
    if op=='add': return plus(a,b)
    if op=='sub': return plus(a,b,-1)
    assert op=='mul'
    out={}
    for (i,j),x in a.items():
        for (k,l),y in b.items(): out[(i+k,j+l)]=out.get((i+k,j+l),0)+x*y
    return {k:v for k,v in out.items() if v}
n0, = [r for r in new['residuals'] if r['gate']=='N0']
leading={j:v for (i,j),v in poly(n0['expr']).items() if i==10}
assert leading == {2:-1}

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
for info in binding['ports'].values():
    data = (new_path.parent / binding['path'] / info['file']).read_bytes()
    raw = gzip.decompress(data)
    assert digest(data) == info['gzip_sha256'] and digest(raw) == info['raw_sha256']
    assert len(raw) == info['raw_bytes']
    if info['file'] == binding['ports']['beta']['file']: assert int.from_bytes(raw, 'big') > 0
for path_key, hash_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert digest((new_path.parent / binding[path_key]).read_bytes()) == binding[hash_key]
print(json.dumps({'status': 'PASS_EXTERNAL_AST_AUDIT', 'retained_residuals': 11,
                  'N0_t10_coefficient': '-beta^2', 'sum_of_squares_degree': '20 for beta != 0',
                  'claim': 'external AST only; no Lean bridge, endpoint, or PDF binding'}, sort_keys=True))
