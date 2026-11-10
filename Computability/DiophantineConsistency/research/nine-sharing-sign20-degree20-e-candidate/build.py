#!/usr/bin/env python3
"""Eliminate the E coordinate from the external sign21 degree-14 seed."""
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
here = Path(__file__).resolve().parent
source = here.parent / 'nine-sharing-sign21-degree14-s-candidate/seed.json'
raw = source.read_bytes()
pin = '85ad59859a6ebc62f8a4de250ac7abf3af904601e8f6c9e696351d5247ea6e81'
assert hashlib.sha256(raw).hexdigest() == pin
seed = json.loads(raw)
row, = [r for r in seed['residuals'] if r['gate'] == 'E']
assert row['kind'] == 'positive' and row['expr'][:2] == ['sub', ['var', 16]]
rhs = row['expr'][2]

def subst(t):
    op = t[0]
    if op == 'var':
        return subst(rhs) if t[1] == 16 else ['var', t[1] - (t[1] > 16)]
    if op in ('num', 'port'):
        return t[:]
    assert op in ('add', 'sub', 'mul') and len(t) == 3
    return [op, subst(t[1]), subst(t[2])]

out = {'schema': 'sign20_degree20_e_candidate_v1',
       'status': 'external source-only candidate; no Lean bridge or endpoint',
       'source': '../nine-sharing-sign21-degree14-s-candidate/seed.json',
       'source_sha256': pin, 'coefficient_binding': seed['coefficient_binding'],
       'fixed_ports': seed['fixed_ports'], 'distinguished_input_coordinate': 0,
       'total_coordinates': 21, 'witness_count': 20,
       'removed_old_coordinate': 16, 'removed_gate': 'E',
       'lift_expression': subst(rhs),
       'output': 'sum of squares of the 11 displayed residuals',
       'residuals': [dict(r, expr=subst(r['expr'])) for r in seed['residuals'] if r['gate'] != 'E']}
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
