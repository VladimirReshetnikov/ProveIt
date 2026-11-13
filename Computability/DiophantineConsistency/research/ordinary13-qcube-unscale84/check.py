#!/usr/bin/env python3
"""Source delta, exact substitution controls and compact44 degree ray; no Lean."""
import gzip, hashlib, json, random
from pathlib import Path

D = Path(__file__).resolve().parents[2]
H = Path(__file__).resolve().parent

def load(path, expected):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == expected
    return json.loads(data)

c = load(H / 'candidate.json', '2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77')
p = load(D / 'research/ordinary13-aux-root87-36/candidate.json', 'abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51')
assert c['witnesses'] == ['s' if x == 'Y' else x for x in p['witnesses']]
assert c['fixed_numerals'] == p['fixed_numerals']
expected = []
for row in p['source']:
    n, op, x, y = row
    if n == 'q3': expected.extend([row, ['Y', '*', 'q3', 's']])
    elif n in ('M', 'g33', 'g34', 'folded_q3Bt'): continue
    elif n == 'g32': expected.append(['g32', '*', 'qm', 'folded_g31'])
    elif n == 'Z': expected.append(['Z', '-', 'g32', 'Bt'])
    elif n == 'g39': expected.append(['g39', '*', 'qm', 'qm'])
    else: expected.append(row)
assert c['source'] == expected and len(expected) == 84
assert len({r[0] for r in expected}) == 84
needed = {'out'}
for n, op, x, y in reversed(expected):
    if n in needed: needed.update((x, y))
assert all(r[0] in needed for r in expected)
assert all(x in needed for x in c['witnesses'] + c['fixed_numerals'])

def calc(graph, env):
    d = env.copy()
    def val(x): return x if isinstance(x, int) else d[x]
    for n, op, x, y in graph['source']:
        a, b = val(x), val(y)
        d[n] = a * b if op == '*' else a + b if op == '+' else a - b
    return d

rng = random.Random(138456)
for _ in range(160):
    env = {x: rng.randrange(-4, 5) for x in c['witnesses'] + c['fixed_numerals']}
    new = calc(c, env)
    old_env = {x: env[x] for x in p['witnesses'] if x != 'Y'}
    old_env.update({x: env[x] for x in p['fixed_numerals']})
    old_env['Y'] = new['Y']
    old_env['r'] = env['r'] - env['s']
    old = calc(p, old_env)
    assert old['Z'] == new['q3'] * new['Z']
    assert old['A0'] == new['q3'] ** 2 * new['A0']
    for name in ('A1', 'Fa', 'g72'): assert old[name] == new[name]

p72 = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = load(p72 / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115 = load(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed = {}
for n, m in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw'] == m['sha256_raw']
    assert b115['ports'][n]['sha256_gzip'] == m['sha256_gzip']
    z = (p72 / m['path']).read_bytes()
    assert hashlib.sha256(z).hexdigest() == m['sha256_gzip']
    raw = gzip.decompress(z)
    assert len(raw) == m['raw_bytes'] and hashlib.sha256(raw).hexdigest() == m['sha256_raw']
    fixed[n] = int.from_bytes(raw, 'little')
assert fixed['beta'] > 0
prime = 1000000007
env = {x: [0, 1] for x in c['witnesses']}
env.update({n: [x % prime] for n, x in fixed.items()})
def trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def add(a, b, sign):
    return trim([((a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)) % prime for i in range(max(len(a), len(b)))])
def mul(a, b):
    z = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): z[i+j] = (z[i+j] + x*y) % prime
    return trim(z)
def val(x): return [x % prime] if isinstance(x, int) else env[x]
for n, op, x, y in expected:
    env[n] = mul(val(x), val(y)) if op == '*' else add(val(x), val(y), 1 if op == '+' else -1)
assert len(env['out']) - 1 == 56 and env['out'][-1] != 0
print(json.dumps({'operations': 84, 'variables': 13, 'all_gates_inputs_ports_live': True,
    'signed_substitution_controls': 160, 'beta_positive': True, 'prime': prime,
    'ray_degree': len(env['out']) - 1, 'ray_leader': env['out'][-1],
    'scope': 'external source and finite controls; positive-zero proof and degree bound require independent review; no Lean/PDF binding'}, sort_keys=True, indent=2))
