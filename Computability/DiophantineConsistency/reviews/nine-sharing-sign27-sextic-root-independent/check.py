#!/usr/bin/env python3
"""Independently audit the source substitution and integer degree argument."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1] / 'research'
PARENT = RESEARCH / 'nine-sharing-sign28-sextic-candidate' / 'seed.json'
CHILD_DIR = RESEARCH / 'nine-sharing-sign27-sextic-normalized-root-candidate'
CHILD = CHILD_DIR / 'seed.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
parent_bytes, child_bytes = PARENT.read_bytes(), CHILD.read_bytes()
assert sha(parent_bytes) == 'b5ea881fefc64c14dafa59c8639a0786224e81b75bb2517eccb1e0021fbb10aa'
assert sha(child_bytes) == '5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d'
old, new = json.loads(parent_bytes), json.loads(child_bytes)
assert old['witness_count'] == 28 and new['witness_count'] == 27
assert new['source_sha256'] == sha(parent_bytes)
assert new['distinguished_input_coordinate'] == 0
oldrows = {r['gate']: r for r in old['residuals']}
newrows = {r['gate']: r for r in new['residuals']}
assert len(oldrows) == 19 and len(newrows) == 18
assert set(oldrows) - set(newrows) == {'N1'}
assert oldrows['N1']['expr'] == ['sub', ['sub', ['mul', ['var', 21], ['var', 21]], ['var', 22]], ['num', 1]]
u = ['var', 21]
root = ['add', u, ['num', 1]]
product = ['mul', u, ['add', u, ['num', 2]]]
assert new['old_root_as_new'] == root and new['old_product_as_new'] == product
assert (new['old_root_coordinate'], new['old_product_coordinate'], new['new_predecessor_coordinate']) == (21, 22, 21)
mapping = {i: ['var', i if i < 22 else i-1] for i in range(29)}
mapping[21], mapping[22] = root, product

def mapped(t):
    tag = t[0]
    if tag == 'var': return mapping[t[1]]
    if tag in ('port', 'num'): return t
    assert tag in ('add', 'sub', 'mul') and len(t) == 3
    return [tag, *(mapped(x) for x in t[1:])]

def degree(t):
    if t[0] == 'var':
        assert 1 <= t[1] <= 27
        return 1
    if t[0] in ('port', 'num'): return 0
    a, b = map(degree, t[1:])
    return a+b if t[0] == 'mul' else max(a, b)

for gate, row in newrows.items():
    a, b = dict(oldrows[gate]), dict(row)
    left, right = a.pop('expr'), b.pop('expr')
    assert a == b and mapped(left) == right
degrees = {gate: degree(row['expr']) for gate, row in newrows.items()}
assert max(degrees.values()) == 3
q3 = newrows['q3']['expr']
q = ['add', ['mul', ['port', 'beta'], ['add', ['var', 1], ['num', 1]]], ['num', 1]]
assert q3 == ['sub', ['var', 15], ['mul', ['mul', q, q], q]]

assert new['coefficient_binding'] == old['coefficient_binding']
binding = new['coefficient_binding']
directory = (CHILD_DIR / binding['path']).resolve()
ports = {}
for name, spec in binding['ports'].items():
    compressed = (directory / spec['file']).read_bytes()
    data = gzip.decompress(compressed)
    assert sha(compressed) == spec['gzip_sha256'] and sha(data) == spec['raw_sha256']
    assert len(data) == spec['raw_bytes']
    number = int.from_bytes(data, 'big')
    assert number.bit_length() == spec['bits']
    ports[name] = {'bits': number.bit_length(), 'raw_sha256': sha(data)}
assert int.from_bytes(gzip.decompress((directory / binding['ports']['beta']['file']).read_bytes()), 'big') > 0
for path_key, sha_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert sha((CHILD_DIR / binding[path_key]).resolve().read_bytes()) == binding[sha_key]

out = {'status': 'PASS_SOURCE_SUBSTITUTION_AND_EXTERNAL_DEGREE', 'parent_sha256': sha(parent_bytes), 'seed_sha256': sha(child_bytes), 'checked_residuals': len(newrows), 'max_residual_syntactic_degree': max(degrees.values()), 'ports': ports, 'scope': 'Structural AST, byte paths and external integer degree only; no Lean or all-model bridge'}
print(json.dumps(out, indent=2, sort_keys=True))
