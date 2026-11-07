#!/usr/bin/env python3
"""Independently check one-step syntactic degrees by variable weights."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] / 'research'
raw = (ROOT / 'nine-sharing-sign27-sextic-normalized-root-candidate' / 'seed.json').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '5bd7f45de28980c6ac9d3974a0087b1d9f8faf9b060b8a115843ea0cc4adff3d'
rows = json.loads(raw)['residuals']
claimed = json.loads((ROOT / 'nine-sharing-sign27-single-positive-cut-survey' / 'result.json').read_bytes())

def natural(t):
    if t[0] in ('var', 'port'): return True
    if t[0] == 'num': return t[1] >= 0
    return t[0] in ('add', 'mul') and all(map(natural, t[1:]))

def weights(t, coordinate=None, substitute_degree=1):
    if t[0] == 'var': return substitute_degree if t[1] == coordinate else 1
    if t[0] in ('port', 'num'): return 0
    a, b = (weights(x, coordinate, substitute_degree) for x in t[1:])
    if t[0] == 'mul': return a + b
    assert t[0] in ('add', 'sub')
    return max(a, b)

def variables(t):
    if t[0] == 'var': return {t[1]}
    if t[0] in ('port', 'num'): return set()
    return variables(t[1]) | variables(t[2])

cases = []
for row in rows:
    expr = row['expr']
    if row['kind'] != 'positive' or expr[0] != 'sub' or expr[1][0] != 'var': continue
    coordinate, rhs = expr[1][1], expr[2]
    if coordinate in variables(rhs) or not natural(rhs): continue
    d = weights(rhs)
    others = {r['gate']: weights(r['expr'], coordinate, d) for r in rows if r is not row}
    maximum = max(others.values())
    cases.append({'coordinate': coordinate, 'gate': row['gate'], 'maximum_residual_syntactic_degree': maximum, 'rows_at_maximum': [r['gate'] for r in rows if r is not row and others[r['gate']] == maximum]})
assert cases == claimed['cases'] and len(cases) == 7 and all(c['maximum_residual_syntactic_degree'] > 3 for c in cases)
print(json.dumps({'status': 'PASS_INDEPENDENT_WEIGHT_RECURSION', 'cases': cases, 'scope': 'one displayed natural positive cut, literal substitution, syntactic degree; no semantic lower bound'}, indent=2, sort_keys=True))
