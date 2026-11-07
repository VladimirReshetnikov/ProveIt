#!/usr/bin/env python3
"""Independently verify the local Nt identity via degree-bounded interpolation."""
import hashlib
import itertools
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
raw = (HERE.parents[1] / 'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json').read_bytes()
digest = hashlib.sha256(raw).hexdigest()
assert digest == '36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25'
rows = json.loads(raw)['residuals']
def contains4(t):
    if t[0] == 'var': return t[1] == 4
    if t[0] in ('num', 'port'): return False
    return any(map(contains4, t[1:]))
assert [r['gate'] for r in rows if contains4(r['expr'])] == ['Nt']
nt = next(r['expr'] for r in rows if r['gate'] == 'Nt')
# Degree bounds in (beta, h, K0, v4) after substituting
# v1=v2=v3=0 and v9=beta*h-K0-1.
def bound(t, i):
    if t[0] == 'num': return 0
    if t[0] == 'var': return {1:(0,0,0,0), 2:(0,0,0,0), 3:(0,0,0,0), 4:(0,0,0,1), 9:(1,1,1,0)}[t[1]][i]
    if t[0] == 'port': return {'beta':(1,0,0,0), 'K0':(0,0,1,0)}[t[1]][i]
    x, y = (bound(z, i) for z in t[1:])
    if t[0] == 'mul': return x+y
    assert t[0] in ('add', 'sub')
    return max(x, y)
def evaluate(t, b, h, k, z):
    if t[0] == 'num': return t[1]
    if t[0] == 'port': return {'beta':b, 'K0':k}[t[1]]
    if t[0] == 'var': return {1:0, 2:0, 3:0, 4:z, 9:b*h-k-1}[t[1]]
    x, y = (evaluate(w, b, h, k, z) for w in t[1:])
    return {'add':lambda:x+y, 'sub':lambda:x-y, 'mul':lambda:x*y}[t[0]]()
degrees = [max(bound(nt, i), d) for i, d in enumerate((2, 1, 0, 1))]
for b, h, k, z in itertools.product(*(range(d+1) for d in degrees)):
    assert evaluate(nt, b, h, k, z) == b*(h*(b-1)-z)-1
print(json.dumps({'status':'PASS_INDEPENDENT_NT_INTERPOLATION', 'source_sha256':digest, 'separate_degree_bounds':degrees, 'scope':'Nt only; no assertion about other rows, full system or Lean'}, indent=2, sort_keys=True))
