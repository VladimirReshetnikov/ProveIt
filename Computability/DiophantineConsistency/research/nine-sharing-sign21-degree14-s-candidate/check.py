#!/usr/bin/env python3
"""Check the external sign22-to-sign21 substitution and degree witness."""
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
old_path = here.parent / 'nine-sharing-sign22-dodecic-ky-candidate/seed.json'
new_path = here / 'seed.json'
digest = lambda b: hashlib.sha256(b).hexdigest()
assert digest(old_path.read_bytes()) == '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
assert digest(new_path.read_bytes()) == '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
old, new = (json.loads(p.read_bytes()) for p in (old_path, new_path))
assert old['witness_count'] == 22 and new['witness_count'] == 21
assert new['total_coordinates'] == 22 and new['distinguished_input_coordinate'] == 0
assert old['fixed_ports'] == new['fixed_ports'] and old['coefficient_binding'] == new['coefficient_binding']
deleted, = [r for r in old['residuals'] if r['gate'] == 'normalized_S']
replacement = ['mul', ['add', ['var', 6], ['num', 1]],
                      ['mul', ['var', 17], ['add', ['var', 17], ['num', 2]]]]
assert deleted['kind'] == 'positive'
assert deleted['expr'] == ['sub', ['var', 21], replacement]
assert new['lift_expression'] == replacement

def matches(a, b):
    op = a[0]
    if op == 'var':
        i = a[1]
        return b == (replacement if i == 21 else ['var', i - (i > 21)])
    if op in ('num', 'port'): return a == b
    return op in ('add', 'sub', 'mul') and len(a) == len(b) == 3 and op == b[0] and matches(a[1], b[1]) and matches(a[2], b[2])

remaining = [r for r in old['residuals'] if r['gate'] != 'normalized_S']
assert len(old['residuals']) == 13 and len(remaining) == len(new['residuals']) == 12
for a, b in zip(remaining, new['residuals']):
    assert a.keys() == b.keys()
    for key in a:
        assert matches(a[key], b[key]) if key == 'expr' else a[key] == b[key]

def degree(t):
    if t[0] == 'var':
        assert 0 <= t[1] < 22
        return 1
    if t[0] in ('num', 'port'): return 0
    assert t[0] in ('add', 'sub', 'mul')
    a, b = degree(t[1]), degree(t[2])
    return a + b if t[0] == 'mul' else max(a, b)

degrees = {r['gate']: degree(r['expr']) for r in new['residuals']}
assert max(degrees.values()) == 7

def plus(a, b, sign=1):
    result = dict(a)
    for k, v in b.items(): result[k] = result.get(k, 0) + sign*v
    return {k: v for k, v in result.items() if v}
def poly(t):
    op = t[0]
    if op == 'num': return {0: t[1]} if t[1] else {}
    if op == 'var': return {1: 1} if t[1] in (6, 17, 21) else {}
    assert op != 'port'
    a, b = poly(t[1]), poly(t[2])
    if op == 'add': return plus(a, b)
    if op == 'sub': return plus(a, b, -1)
    assert op == 'mul'
    out = {}
    for i, x in a.items():
        for j, y in b.items(): out[i+j] = out.get(i+j, 0) + x*y
    return {k: v for k, v in out.items() if v}
na, = [r for r in new['residuals'] if r['gate'] == 'Na']
na_poly = poly(na['expr'])
assert na_poly == {7: -1, 6: -6, 5: -13, 4: -12, 3: -4}

binding = new['coefficient_binding']
assert (new_path.parent / binding['path']).resolve() == (old_path.parent / old['coefficient_binding']['path']).resolve()
files = {}
for name, record in binding['ports'].items():
    packed = (new_path.parent / binding['path'] / record['file']).read_bytes()
    raw = gzip.decompress(packed)
    assert digest(packed) == record['gzip_sha256'] and digest(raw) == record['raw_sha256']
    assert len(raw) == record['raw_bytes']
    files[name] = digest(packed)

def evaluate(t, coords, ports):
    op = t[0]
    if op == 'var': return coords[t[1]]
    if op == 'num': return t[1]
    if op == 'port': return ports[t[1]]
    a, b = evaluate(t[1], coords, ports), evaluate(t[2], coords, ports)
    return a+b if op == 'add' else a-b if op == 'sub' else a*b
rng = random.Random(2221)
for _ in range(16):
    coords = [rng.randrange(4) for _ in range(22)]
    ports = {name: rng.randrange(5) for name in new['fixed_ports']}
    k = evaluate(replacement, coords, ports)
    lifted = coords[:21] + [k] + coords[21:]
    assert k >= 0 and len(lifted) == 23 and lifted[0] == coords[0]
    assert evaluate(deleted['expr'], lifted, ports) == 0
    assert [evaluate(r['expr'], lifted, ports) for r in remaining] == [evaluate(r['expr'], coords, ports) for r in new['residuals']]

assert json.loads(subprocess.run([sys.executable, '-I', '-S', '-B', str(here/'build.py'), '--check'],
                                 capture_output=True, text=True, check=True, timeout=120).stdout)['status'] == 'PASS'
print(json.dumps({'status': 'PASS_EXTERNAL_CHECK', 'source_sha256': digest(old_path.read_bytes()),
                  'candidate_sha256': digest(new_path.read_bytes()), 'residuals': 12,
                  'residual_syntactic_degrees': degrees,
                  'Na_univariate_coefficients': na_poly, 'exact_seed_degree': 14,
                  'coefficient_gzip_sha256': files, 'finite_natural_lifts': 16,
                  'scope': 'external fixed-port AST; no Lean bridge or endpoint'}, indent=2, sort_keys=True))
