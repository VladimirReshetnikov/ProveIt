#!/usr/bin/env python3
"""Independent reduced-ring evaluation of the restricted q3-cut survey."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1] / 'research'
raw = (RESEARCH / 'nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25'
rows = json.loads(raw)['residuals']
claimed = json.loads((RESEARCH / 'nine-sharing-sign26-q3-single-cut-survey/result.json').read_bytes())
N, AI, QI = 32, 31, 15
Z = (0,) * N
def const(n): return {Z: n} if n else {}
def var(i):
    a = list(Z); a[i] = 1
    return {tuple(a): 1}
def plus(x, y, sign=1):
    z = x.copy()
    for m, coefficient in y.items(): z[m] = z.get(m, 0) + sign*coefficient
    return {m: c for m, c in z.items() if c}
def reduced(poly):
    pending = list(poly.items()); out = {}
    while pending:
        m, c = pending.pop()
        if m[AI] < 3:
            out[m] = out.get(m, 0) + c
            continue
        base = list(m); base[AI] -= 3
        for index, power, scale in [(QI, 1, 1), (AI, 2, -3), (AI, 1, -3), (None, 0, -1)]:
            new = base.copy()
            if index is not None: new[index] += power
            pending.append((tuple(new), c*scale))
    return {m: c for m, c in out.items() if c}
def mul(x, y):
    out = {}
    for m, c in x.items():
        for n, d in y.items():
            z = tuple(a+b for a, b in zip(m, n)); out[z] = out.get(z, 0) + c*d
    return reduced(out)
ports = {'beta': 27, 'K0': 28, 'MC': 29, 'MF': 30}
abstract_a = ['mul', ['port', 'beta'], ['add', ['var', 1], ['num', 1]]]
def evaluate(t, coordinate=None, replacement=None):
    if t == abstract_a: return var(AI)
    if t[0] == 'num': return const(t[1])
    if t[0] == 'port': return var(ports[t[1]])
    if t[0] == 'var': return replacement if t[1] == coordinate else var(t[1])
    x, y = (evaluate(z, coordinate, replacement) for z in t[1:])
    if t[0] == 'mul': return mul(x, y)
    assert t[0] in ('add', 'sub')
    return plus(x, y, 1 if t[0] == 'add' else -1)
def degree(poly): return max((sum(m[:27]) + m[AI] for m in poly), default=0)

cases = []
for cut in rows:
    e = cut['expr']
    if e[0] != 'sub' or e[1][0] != 'var' or e[1][1] in (0, 15): continue
    i = e[1][1]; replacement = evaluate(e[2])
    # No selected RHS contains its own coordinate.
    assert all(m[i] == 0 for m in replacement)
    ds = []
    for row in rows:
        if row is cut: continue
        # The survey retains q3 itself unreduced; its formal degree is 3.
        d = 3 if row['gate'] == 'q3' else degree(evaluate(row['expr'], i, replacement))
        ds.append((row['gate'], d))
    maximum = max(d for _, d in ds)
    cases.append({'gate': cut['gate'], 'kind': cut['kind'], 'coordinate': i, 'maximum_remainder_degree': maximum, 'rows_at_maximum': [name for name, d in ds if d == maximum]})
assert cases == claimed['cases'] and len(cases) == 10 and all(c['maximum_remainder_degree'] > 3 for c in cases)
print(json.dumps({'status': 'PASS_INDEPENDENT_REDUCED_RING_EVALUATION', 'source_sha256': hashlib.sha256(raw).hexdigest(), 'cases': cases, 'scope': 'specified single cuts and monic formal q3 remainder only; no semantic lower bound'}, indent=2, sort_keys=True))
