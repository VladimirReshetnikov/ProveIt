#!/usr/bin/env python3
"""Check the external sign19-to-sign18 substitution and degree witness."""
import gzip
import hashlib
import json
import random
import subprocess
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
old_path = here.parent / 'nine-sharing-sign19-degree44-y-candidate/seed.json'
new_path = here / 'seed.json'
digest = lambda b: hashlib.sha256(b).hexdigest()
assert digest(old_path.read_bytes()) == '01bae1f7680ce07eb5c041d5ae6a625ead9e79e1c968472521458475a4eb94f1'
assert digest(new_path.read_bytes()) == 'd3fd0a00ed9f803a5c002481dbfb22aafe9a5ba34ac89c90069cefbdcaada3fb'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 19 and new['witness_count'] == 18
assert new['total_coordinates'] == 19 and new['distinguished_input_coordinate'] == 0
assert old['fixed_ports'] == new['fixed_ports'] and old['coefficient_binding'] == new['coefficient_binding']
deleted, = [r for r in old['residuals'] if r['gate'] == 'main_root']
lhs,rhs=deleted['expr'][1:];assert deleted['expr'][0]=='sub' and lhs==['add',['var',15],['num',1]]
first,second,third=rhs[1][1],rhs[1][2],rhs[2];A=first[2]
assert first==['mul',['add',['var',9],['num',1]],A]
assert A==['add',['mul',['port','beta'],['add',['var',1],['num',1]]],['num',1]]
replacement=['add',['add',['add',['mul',['var',9],A],A[1]],second],third]
assert deleted['kind']=='positive' and new['lift_expression']==replacement
def nonnegative_syntax(t):
    if t[0]=='num': return type(t[1]) is int and t[1]>=0
    if t[0] in ('var','port'): return True
    return t[0] in ('add','mul') and nonnegative_syntax(t[1]) and nonnegative_syntax(t[2])
assert nonnegative_syntax(replacement)

def matches(a, b):
    op = a[0]
    if op == 'var':
        i = a[1]
        return b == (replacement if i == 15 else ['var', i - (i > 15)])
    if op in ('num', 'port'): return a == b
    return op in ('add', 'sub', 'mul') and len(a) == len(b) == 3 and op == b[0] and matches(a[1], b[1]) and matches(a[2], b[2])

remaining = [r for r in old['residuals'] if r['gate'] != 'main_root']
assert len(old['residuals']) == 10 and len(remaining) == len(new['residuals']) == 9
for a, b in zip(remaining, new['residuals']):
    assert a.keys() == b.keys()
    for key in a:
        assert matches(a[key], b[key]) if key == 'expr' else a[key] == b[key]

def degree(t):
    if t[0] == 'var':
        assert 0 <= t[1] < 19
        return 1
    if t[0] in ('num', 'port'): return 0
    assert t[0] in ('add', 'sub', 'mul')
    a, b = degree(t[1]), degree(t[2])
    return a + b if t[0] == 'mul' else max(a, b)
degrees = {r['gate']: degree(r['expr']) for r in new['residuals']}
assert max(degrees.values()) == 47

# Exact symbolic Na specialization in Z[t,b], where b is the beta port.
def plus(a, b, sign=1):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, 0) + sign*v
    return {k: v for k, v in out.items() if v}
def poly(t):
    op = t[0]
    if op == 'num': return {(0,0): t[1]} if t[1] else {}
    if op == 'var': return {(1,0): 1} if 1 <= t[1] <= 18 else {}
    if op == 'port':
        assert t[1] == 'beta'
        return {(0,1): 1}
    a, b = poly(t[1]), poly(t[2])
    if op == 'add': return plus(a,b)
    if op == 'sub': return plus(a,b,-1)
    assert op == 'mul'
    out = {}
    for (i,j), x in a.items():
        for (k,l), y in b.items(): out[(i+k,j+l)] = out.get((i+k,j+l), 0) + x*y
    return {k: v for k,v in out.items() if v}
n0, = [r for r in new['residuals'] if r['gate'] == 'Na']
def uses_input(t):
    return t[0] == 'var' and t[1] == 0 if t[0] in ('var','num','port') else uses_input(t[1]) or uses_input(t[2])
assert not uses_input(n0['expr'])
special = poly(n0['expr'])
assert {k:v for k,v in special.items() if k[0] == 47} == {(47,28): -16}
assert max(t for t,_ in special) == 47

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
files = {}
for name, record in binding['ports'].items():
    packed = (new_path.parent / binding['path'] / record['file']).read_bytes()
    raw = gzip.decompress(packed)
    assert digest(packed) == record['gzip_sha256'] and digest(raw) == record['raw_sha256']
    assert len(raw) == record['raw_bytes']
    if name == 'beta': assert int.from_bytes(raw, 'big') > 0
    files[name] = digest(packed)

def evaluate(t, coords, ports):
    op = t[0]
    if op == 'var': return coords[t[1]]
    if op == 'num': return t[1]
    if op == 'port': return ports[t[1]]
    a, b = evaluate(t[1], coords, ports), evaluate(t[2], coords, ports)
    return a+b if op == 'add' else a-b if op == 'sub' else a*b
rng = random.Random(2120)
for _ in range(16):
    coords = [rng.randrange(4) for _ in range(19)]
    ports = {name: rng.randrange(5) for name in new['fixed_ports']}
    k = evaluate(replacement, coords, ports)
    lifted = coords[:15] + [k] + coords[15:]
    assert k >= 0 and len(lifted) == 20 and lifted[0] == coords[0]
    assert evaluate(deleted['expr'], lifted, ports) == 0
    assert [evaluate(r['expr'], lifted, ports) for r in remaining] == [evaluate(r['expr'], coords, ports) for r in new['residuals']]
assert json.loads(subprocess.run([sys.executable, '-I', '-S', '-B', str(here/'build.py'), '--check'],
                                 capture_output=True, text=True, check=True, timeout=120).stdout)['status'] == 'PASS'
print(json.dumps({'status': 'PASS_EXTERNAL_CHECK', 'source_sha256': digest(old_path.read_bytes()),
                  'candidate_sha256': digest(new_path.read_bytes()), 'residuals': 9,
                  'residual_syntactic_degrees': degrees,
                  'Na_t47_coefficient': '-16*beta^28', 'exact_seed_degree_if_beta_nonzero': 94,
                  'coefficient_gzip_sha256': files, 'finite_natural_lifts': 16,
                  'scope': 'external fixed-port AST; no Lean bridge or endpoint'}, indent=2, sort_keys=True))
