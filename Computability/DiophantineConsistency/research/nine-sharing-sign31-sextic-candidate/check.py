#!/usr/bin/env python3
"""Check syntactic degree and exercise the 31-to-32 reconstruction externally."""
import hashlib
import json
import random
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
old = json.loads((HERE.parent / 'nine-sharing-sign32-sextic-candidate-v2' / 'seed.json').read_bytes())
raw = (HERE / 'seed.json').read_bytes()
new = json.loads(raw)
assert new['witness_count'] == 31 and len(new['residuals']) == 22
assert [r['gate'] for r in old['residuals'] if r['gate'] != 'f2'] == [r['gate'] for r in new['residuals']]

def degree(t):
    op = t[0]
    if op == 'var':
        assert 1 <= t[1] <= 31  # input 0 remains unused
        return 1
    if op in ('num', 'port'):
        return 0
    a, b = degree(t[1]), degree(t[2])
    if op in ('add', 'sub'):
        return max(a, b)
    assert op == 'mul'
    return a + b

degrees = {r['gate']: degree(r['expr']) for r in new['residuals']}
assert max(degrees.values()) == 3
assert new['residuals'][0] == old['residuals'][0]
assert new['residuals'][0]['gate'] == 'q3'

def evaluate(t, values, ports):
    op = t[0]
    if op == 'var': return values[t[1]]
    if op == 'num': return t[1]
    if op == 'port': return ports[t[1]]
    a, b = evaluate(t[1], values, ports), evaluate(t[2], values, ports)
    return {'add': lambda: a+b, 'sub': lambda: a-b, 'mul': lambda: a*b}[op]()

rng = random.Random(3106)
for _ in range(16):
    values = [rng.randrange(4) for _ in range(32)]
    ports = {p: rng.randrange(1, 5) for p in new['fixed_ports']}
    lifted = values[:27] + [(values[5]+1)**2] + values[27:]
    by_gate = {r['gate']: evaluate(r['expr'], lifted, ports) for r in old['residuals']}
    assert by_gate['f2'] == 0
    assert all(evaluate(r['expr'], values, ports) == by_gate[r['gate']] for r in new['residuals'])

print(json.dumps({'status': 'PASS_EXTERNAL_CHECKS_ONLY', 'seed_sha256': hashlib.sha256(raw).hexdigest(), 'degrees': degrees, 'finite_controls': 16}, indent=2, sort_keys=True))
