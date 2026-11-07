#!/usr/bin/env python3
"""Check the local identity independently via bounded polynomial interpolation."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
raw = (HERE.parents[1] / 'research/nine-sharing-sign27-sextic-normalized-root-candidate/seed.json').read_bytes()
digest = hashlib.sha256(raw).hexdigest()
assert digest == '5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d'
rows = json.loads(raw)['residuals']

def has_v3(t):
    if t[0] == 'var': return t[1] == 3
    if t[0] in ('port', 'num'): return False
    return any(map(has_v3, t[1:]))
assert [r['gate'] for r in rows if has_v3(r['expr'])] == ['gap', 'Nt']
targets = {r['gate']: r['expr'] for r in rows if r['gate'] in ('gap', 'Nt')}
assert len(targets) == 2

# Each substitution below is a bivariate polynomial. Compute upper bounds
# separately in a and K, then evaluate a grid larger than both bounds.
def degree(t, variable):
    if t[0] == 'num': return 0
    if t[0] == 'var':
        return {1: (0, 0), 2: (0, 0), 3: (0, 0), 4: (1, 1), 9: (1, 1), 22: (2, 0)}[t[1]][variable]
    if t[0] == 'port': return {'beta': (1, 0), 'K0': (0, 1)}[t[1]][variable]
    a, b = (degree(x, variable) for x in t[1:])
    if t[0] == 'mul': return a+b
    assert t[0] in ('add', 'sub')
    return max(a, b)

def evaluate(t, a, k):
    values = {1: 0, 2: 0, 3: -2, 4: a*(k+1)+k+2, 9: (a-1)*k+a, 22: a*a-1}
    if t[0] == 'var': return values[t[1]]
    if t[0] == 'port': return {'beta': a, 'K0': k}[t[1]]
    if t[0] == 'num': return t[1]
    x, y = (evaluate(z, a, k) for z in t[1:])
    return {'add': lambda: x+y, 'sub': lambda: x-y, 'mul': lambda: x*y}[t[0]]()

bounds = {name: [degree(t, 0), degree(t, 1)] for name, t in targets.items()}
for name, t in targets.items():
    da, dk = bounds[name]
    for a in range(da + 1):
        for k in range(dk + 1):
            assert evaluate(t, a, k) == 0
print(json.dumps({'status': 'PASS_INDEPENDENT_POLYNOMIAL_INTERPOLATION', 'source_sha256': digest, 'separate_degree_bounds': bounds, 'scope': 'gap and Nt only; no full-system counterexample or Lean theorem'}, indent=2, sort_keys=True))
