#!/usr/bin/env python3
"""Eliminate the normalized_S coordinate from the external sign22 seed."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
source = here.parent / 'nine-sharing-sign22-dodecic-ky-candidate/seed.json'
raw = source.read_bytes()
pin = '3746dacafb661a8bab30caee81ec3b2130915a8b31adf8fe3630f6a541574f37'
assert hashlib.sha256(raw).hexdigest() == pin
seed = json.loads(raw)
row, = [r for r in seed['residuals'] if r['gate'] == 'normalized_S']
assert row['kind'] == 'positive' and row['expr'][:2] == ['sub', ['var', 21]]
rhs = row['expr'][2]

def subst(t):
    op = t[0]
    if op == 'var':
        return subst(rhs) if t[1] == 21 else ['var', t[1] - (t[1] > 21)]
    if op in ('num', 'port'): return t[:]
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    return [op, subst(t[1]), subst(t[2])]

out = {'schema': 'sign21_degree14_s_candidate_v1',
       'status': 'external source-only candidate; no Lean bridge or endpoint',
       'source': '../nine-sharing-sign22-dodecic-ky-candidate/seed.json',
       'source_sha256': pin, 'coefficient_binding': seed['coefficient_binding'],
       'fixed_ports': seed['fixed_ports'], 'distinguished_input_coordinate': 0,
       'total_coordinates': 22, 'witness_count': 21,
       'removed_old_coordinate': 21, 'removed_gate': 'normalized_S',
       'lift_expression': subst(rhs),
       'output': 'sum of squares of the 12 displayed residuals',
       'residuals': [dict(r, expr=subst(r['expr'])) for r in seed['residuals'] if r['gate'] != 'normalized_S']}
encoded = json.dumps(out, indent=2, sort_keys=True) + '\n'
target = here / 'seed.json'
if sys.argv[1:] == ['--write']:
    if target.exists(): raise SystemExit('refusing to overwrite seed')
    target.write_text(encoded)
elif sys.argv[1:] == ['--check']:
    assert target.read_text() == encoded
    print(json.dumps({'status': 'PASS', 'seed_sha256': hashlib.sha256(encoded.encode()).hexdigest()}, sort_keys=True))
else:
    raise SystemExit('use --write or --check')
