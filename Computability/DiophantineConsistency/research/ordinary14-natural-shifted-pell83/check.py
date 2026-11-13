#!/usr/bin/env python3
"""Check the shifted-Pell graph and its authenticated modular degree ray."""
import gzip, hashlib, json, random
from pathlib import Path
D = Path(__file__).resolve().parents[2]
H = Path(__file__).resolve().parent

def load(path, sha):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == sha
    return json.loads(data)

c = load(H / 'candidate.json', '36c910fe9a6c59eeab8bfd97583dae3c27d7680f848046ed84622d9d8dd45d19')
p = load(D / 'research/ordinary14-root74-natural-forced82/candidate.json', '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a')
expected = []
for row in p['source']:
    n = row[0]
    if n in {'g30', 'g38', 'g40'}:
        continue
    if n == 'F0':
        expected += [['t2', '*', 'n_t', 'n_t'], ['twot', '*', 2, 'n_t'],
                     ['twot_minus_k', '-', 'twot', 'k'], ['ell_times', '*', 'ell', 'twot_minus_k'],
                     ['F0', '+', 't2', 'ell_times']]
    else:
        expected.append(row)
assert c['source'] == expected and c['operations'] == len(expected) == 83
assert c['witnesses'] == ['n_t' if x == 'n_r' else x for x in p['witnesses']]
assert c['domain'] == 'nonnegative integers' and c['fixed_numerals'] == p['fixed_numerals']
known = set(c['witnesses'] + c['fixed_numerals'])
for n, op, x, y in expected:
    assert n not in known and op in ('+', '-', '*')
    assert all(isinstance(v, int) or v in known for v in (x, y))
    known.add(n)
needed = {'out'}
for n, op, x, y in reversed(expected):
    if n in needed:
        needed.update((x, y))
assert all(row[0] in needed for row in expected)
assert all(x in needed for x in c['witnesses'] + c['fixed_numerals'])

def calc(graph, env):
    d = env.copy()
    def val(x): return x if isinstance(x, int) else d[x]
    for n, op, x, y in graph['source']:
        a, b = val(x), val(y)
        d[n] = a * b if op == '*' else a + b if op == '+' else a - b
    return d

rng = random.Random(147597)
for _ in range(200):
    vals = {x: rng.randrange(-5, 6) for x in c['witnesses'] + c['fixed_numerals']}
    new = calc(c, vals)
    oldvals = vals.copy()
    oldvals['n_r'] = new['ell'] + vals['n_t']
    old = calc(p, oldvals)
    assert new['F0'] == old['F0'] and new['out'] == old['out']

p72 = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = load(p72 / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115 = load(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed = {}
for n, m in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw'] == m['sha256_raw'] and b115['ports'][n]['sha256_gzip'] == m['sha256_gzip']
    z = (p72 / m['path']).read_bytes()
    assert hashlib.sha256(z).hexdigest() == m['sha256_gzip']
    raw = gzip.decompress(z)
    assert len(raw) == m['raw_bytes'] and hashlib.sha256(raw).hexdigest() == m['sha256_raw']
    fixed[n] = int.from_bytes(raw, 'little')
assert fixed['beta'] > 0 and fixed['K0'] >= 0
prime = 1000000007
env = {x: [0, 1] for x in c['witnesses']}
env['n_t'] = [0, 2]  # Avoid the special cancellation 2t = eta + zeta.
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
assert len(env['out']) - 1 == 97 and env['out'][-1] == 979034495
print(json.dumps({'operations': 83, 'variables': 14, 'all_inputs_nonnegative': True,
                  'all_gates_inputs_ports_live': True, 'signed_identity_tests': 200,
                  'prime': prime, 'ray_degree': len(env['out']) - 1, 'ray_leader': env['out'][-1],
                  'factor_ray_degrees': {n: len(env[n])-1 for n in ['F0', 'F1', 'Fa', 'Fs', 'guard']},
                  'scope': 'external natural-domain shifted-Pell map; no Lean theorem or PDF binding'}, sort_keys=True, indent=2))
