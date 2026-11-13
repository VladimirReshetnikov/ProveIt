#!/usr/bin/env python3
"""Check a forced-positivity coordinate change; this is not a Lean proof."""
from pathlib import Path
import gzip, hashlib, json, random

P = Path(__file__).resolve().parent
D = P.parents[1]
H = lambda data: hashlib.sha256(data).hexdigest()
def load(path, digest):
    data = path.read_bytes()
    assert H(data) == digest, (str(path), H(data))
    return json.loads(data)

a = load(D / 'research/ordinary14-root74-natural-cancel85/candidate.json',
         '24a5ddfdabeae36eb40867239fdc5dfd53ba60d611f0e83268ffb9bfbac85957')
b = load(P / 'candidate.json',
         '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a')
assert a['domain'] == b['domain'] == 'nonnegative integers'
assert a['witnesses'] == b['witnesses'] and a['fixed_numerals'] == b['fixed_numerals']
assert b['parent_sha256'] == H((D / 'research/ordinary14-root74-natural-cancel85/candidate.json').read_bytes())
assert a['operations'] == len(a['source']) == 85 and b['operations'] == len(b['source']) == 82
assert a['output'] == b['output'] == 'out'
removed = {'f': 'n_f', 'r': 'n_r', 'y': 'n_y'}
for n in removed:
    assert [n, '+', removed[n], 1] in a['source']
expected = [[n, op, removed.get(x, x), removed.get(y, y)]
            for n, op, x, y in a['source'] if n not in removed]
assert b['source'] == expected

known = set(b['witnesses'] + b['fixed_numerals'])
assert len(known) == 18
for n, op, x, y in b['source']:
    assert n not in known and op in ('+', '-', '*')
    assert all(type(z) is int or z in known for z in (x, y))
    known.add(n)
live = {'out'}
for n, op, x, y in reversed(b['source']):
    if n in live:
        live.update(z for z in (x, y) if isinstance(z, str))
assert all(n in live for n, _, _, _ in b['source'])
assert set(b['witnesses'] + b['fixed_numerals']) <= live

# The whole DAG is identical after the three affine input substitutions.
# This also holds over arbitrary signed inputs and arbitrary integer ports.
def calc(g, env):
    e = env.copy()
    for n, op, x, y in g['source']:
        x = x if type(x) is int else e[x]
        y = y if type(y) is int else e[y]
        e[n] = x + y if op == '+' else x - y if op == '-' else x * y
    return e['out']
rng = random.Random(147482)
for _ in range(200):
    eb = {v: rng.randrange(-3, 5) for v in b['witnesses']}
    eb.update({v: rng.randrange(-3, 5) for v in b['fixed_numerals']})
    ea = eb.copy()
    for n in removed.values():
        ea[n] -= 1
    assert calc(a, ea) == calc(b, eb)

# Independently authenticate the specialized ports and compute the all-inputs-t
# ray. The affine substitution preserves the parent's degree upper bound 107.
p72 = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind = load(p72 / 'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115 = load(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json',
            'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed = {}
for n, m in bind['ports'].items():
    assert b115['ports'][n]['sha256_raw'] == m['sha256_raw']
    assert b115['ports'][n]['sha256_gzip'] == m['sha256_gzip']
    data = (p72 / m['path']).read_bytes()
    assert H(data) == m['sha256_gzip']
    raw = gzip.decompress(data)
    assert len(raw) == m['raw_bytes'] and H(raw) == m['sha256_raw']
    fixed[n] = int.from_bytes(raw, 'little')
assert set(fixed) == set(b['fixed_numerals'])
prime = 1000000007
def trim(a):
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def add(a, b, sign):
    return trim([((a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)) % prime
                 for i in range(max(len(a), len(b)))])
def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] = (out[i+j] + x*y) % prime
    return trim(out)
e = {v: [0, 1] for v in b['witnesses']}
e.update({v: [x % prime] for v, x in fixed.items()})
def val(x): return [x % prime] if type(x) is int else e[x]
for n, op, x, y in b['source']:
    x, y = val(x), val(y)
    e[n] = mul(x, y) if op == '*' else add(x, y, 1 if op == '+' else -1)
assert len(e['out']) - 1 == 107 and e['out'][-1] == 419359493
print(json.dumps({'scope': 'external natural-zero existence equivalence; no Lean or PDF binding',
                  'inputs': 14, 'operations': 82, 'removed_input_shifts': sorted(removed),
                  'all_gates_inputs_ports_live': True, 'signed_graph_controls': 200,
                  'degree_upper_inherited_from_85': 107, 'ray_prime': prime,
                  'ray_degree': len(e['out']) - 1, 'ray_leader': e['out'][-1]},
                 sort_keys=True, indent=2))
