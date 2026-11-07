#!/usr/bin/env python3
"""Check external degree and finite controls for reverse reconstruction."""
import hashlib
import json
import random
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
old = json.loads((HERE.parent / 'nine-sharing-sign31-sextic-candidate' / 'seed.json').read_bytes())
raw = (HERE / 'seed.json').read_bytes()
new = json.loads(raw)
assert new['witness_count'] == 28 and len(new['residuals']) == 19
assert [s['gate'] for s in new['elimination_steps']] == ['X', 'c2', 'normalized_S2']
assert [r['gate'] for r in old['residuals'] if r['gate'] not in ('X', 'c2', 'normalized_S2')] == [r['gate'] for r in new['residuals']]
assert new['residuals'][0] == old['residuals'][0] and new['residuals'][0]['gate'] == 'q3'

def degree(t):
    op = t[0]
    if op == 'var':
        assert 1 <= t[1] <= 28
        return 1
    if op in ('num', 'port'): return 0
    a, b = degree(t[1]), degree(t[2])
    if op in ('add', 'sub'): return max(a, b)
    assert op == 'mul'
    return a + b

degrees = {r['gate']: degree(r['expr']) for r in new['residuals']}
assert max(degrees.values()) == 3

def evaluate(t, values, ports):
    op = t[0]
    if op == 'var': return values[t[1]]
    if op == 'num': return t[1]
    if op == 'port': return ports[t[1]]
    a, b = evaluate(t[1], values, ports), evaluate(t[2], values, ports)
    return {'add': lambda: a+b, 'sub': lambda: a-b, 'mul': lambda: a*b}[op]()

rng = random.Random(2806)
for _ in range(16):
    values = [rng.randrange(4) for _ in range(29)]
    ports = {p: rng.randrange(1, 5) for p in new['fixed_ports']}
    lifted = values[:]
    for step in reversed(new['elimination_steps']):
        i = step['old_coordinate_at_step']
        lifted.insert(i, 0)
        lifted[i] = evaluate(step['replacement_before_drop'], lifted, ports)
    assert len(lifted) == 32 and all(v >= 0 for v in lifted)
    by_gate = {r['gate']: evaluate(r['expr'], lifted, ports) for r in old['residuals']}
    assert all(by_gate[s['gate']] == 0 for s in new['elimination_steps'])
    assert all(evaluate(r['expr'], values, ports) == by_gate[r['gate']] for r in new['residuals'])

print(json.dumps({'status': 'PASS_EXTERNAL_CHECKS_ONLY', 'seed_sha256': hashlib.sha256(raw).hexdigest(), 'degrees': degrees, 'finite_controls': 16}, indent=2, sort_keys=True))
