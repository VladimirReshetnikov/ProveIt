#!/usr/bin/env python3
"""Independently audit 26-seed polynomial congruences and coefficient bytes."""
import gzip
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1] / 'research'
old_bytes = (RESEARCH / 'nine-sharing-sign27-sextic-normalized-root-candidate/seed.json').read_bytes()
child_dir = RESEARCH / 'nine-sharing-sign26-sextic-gap-congruence-candidate'
new_bytes = (child_dir / 'seed.json').read_bytes()
sha = lambda b: hashlib.sha256(b).hexdigest()
assert sha(old_bytes) == '5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d'
assert sha(new_bytes) == '36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25'
old, new = json.loads(old_bytes), json.loads(new_bytes)
assert new['source_sha256'] == sha(old_bytes) and new['witness_count'] == 26
assert new['distinguished_input_coordinate'] == 0 and new['old_gap_coordinate'] == 22
before = {r['gate']: r for r in old['residuals']}
after = {r['gate']: r for r in new['residuals']}
assert len(before) == 18 and len(after) == 17 and set(before)-set(after) == {'gap'}

# Sparse polynomials keyed by fixed-length exponent tuples, with integer coefficients.
N = 31
zero_exp = (0,) * N
def c(n): return {zero_exp: n} if n else {}
def var(i):
    key = list(zero_exp); key[i] = 1
    return {tuple(key): 1}
def plus(x, y, sign=1):
    z = x.copy()
    for m, coefficient in y.items(): z[m] = z.get(m, 0) + sign*coefficient
    return {m: coefficient for m, coefficient in z.items() if coefficient}
def times(x, y):
    z = {}
    for m, p in x.items():
        for n, q in y.items():
            key = tuple(a+b for a, b in zip(m, n))
            z[key] = z.get(key, 0) + p*q
    return {m: coefficient for m, coefficient in z.items() if coefficient}

v = [var(i) for i in range(27)]
ports = {name: var(i+27) for i, name in enumerate(('beta', 'K0', 'MC', 'MF'))}
one = c(1)
a = times(ports['beta'], plus(v[1], one))
q, n, t = plus(a, one), plus(v[2], one), plus(v[3], one)
g = plus(plus(times(a, q), t), times(a, n), -1)

def poly(tree, old_side=False):
    op = tree[0]
    if op == 'num': return c(tree[1])
    if op == 'port': return ports[tree[1]]
    if op == 'var':
        i = tree[1]
        if old_side and i == 22: return g
        return v[i-1 if old_side and i > 22 else i]
    x, y = (poly(z, old_side) for z in tree[1:])
    if op == 'mul': return times(x, y)
    assert op in ('add', 'sub')
    return plus(x, y, 1 if op == 'add' else -1)

assert not poly(before['gap']['expr'], True)
q3 = poly(after['q3']['expr'])
expected_difference = times(plus(a, n, -1), q3)
for gate, row in after.items():
    x, y = dict(before[gate]), dict(row)
    old_expr, new_expr = x.pop('expr'), y.pop('expr')
    assert x == y
    diff = plus(poly(old_expr, True), poly(new_expr), -1)
    assert diff == (plus({}, expected_difference, -1) if gate in ('tau', 'cTminusR') else {})

H = plus(ports['K0'], plus(v[9], one))
f_minus_one = v[4]
nt_formula = plus(plus(times(H, plus(plus(q, n, -1), t, -1)), n, -1), times(f_minus_one, a), -1)
assert poly(after['Nt']['expr']) == nt_formula

def degree(tree):
    if tree[0] == 'var':
        assert 1 <= tree[1] <= 26
        return 1
    if tree[0] in ('num', 'port'): return 0
    x, y = map(degree, tree[1:])
    return x+y if tree[0] == 'mul' else max(x, y)
assert max(degree(r['expr']) for r in after.values()) == 3
assert before['q3'] == after['q3']
qast = ['add', ['mul', ['port', 'beta'], ['add', ['var', 1], ['num', 1]]], ['num', 1]]
assert after['q3']['expr'] == ['sub', ['var', 15], ['mul', ['mul', qast, qast], qast]]
assert new['coefficient_binding'] == old['coefficient_binding']
binding = new['coefficient_binding']; directory = (child_dir / binding['path']).resolve()
ports_verified = {}
for name, spec in binding['ports'].items():
    compressed = (directory / spec['file']).read_bytes(); data = gzip.decompress(compressed)
    assert sha(compressed) == spec['gzip_sha256'] and sha(data) == spec['raw_sha256']
    assert len(data) == spec['raw_bytes'] and int.from_bytes(data, 'big').bit_length() == spec['bits']
    ports_verified[name] = spec['bits']
assert ports_verified['beta'] > 0
for path_key, sha_key in [('certificate', 'certificate_sha256'), ('ordinary_proof', 'ordinary_proof_sha256')]:
    assert sha((child_dir / binding[path_key]).resolve().read_bytes()) == binding[sha_key]

print(json.dumps({'status': 'PASS_INDEPENDENT_FORMAL_CONGRUENCES', 'seed_sha256': sha(new_bytes), 'retained_residuals': len(after), 'modified_rows': ['tau', 'cTminusR'], 'max_residual_syntactic_degree': 3, 'ports_bit_lengths': ports_verified, 'scope': 'formal integer polynomial identities and byte paths; no all-model or Lean bridge'}, indent=2, sort_keys=True))
