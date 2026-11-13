#!/usr/bin/env python3
"""External graph/degree checks for the 13-input natural C-fold candidate; no Lean."""
from pathlib import Path
import gzip, hashlib, json, random
P = Path(__file__).resolve().parent
D = P.parents[1]
def digest(b): return hashlib.sha256(b).hexdigest()
def load(path, sha):
    b = path.read_bytes(); assert digest(b) == sha, str(path); return json.loads(b)
a = load(D/'research/ordinary13-cfold88-28/candidate.json', '9497efb00c1059897dd6d57522267af90910224f2d37f8901b99dfc28086e333')
b = load(P/'candidate.json', '8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
assert b['parent_sha256'] == digest((D/'research/ordinary13-cfold88-28/candidate.json').read_bytes())
assert a['domain'] == 'strictly positive integers' and b['domain'] == 'nonnegative integers'
assert b['witnesses'] == ['n_'+n for n in a['witnesses']] and a['fixed_numerals'] == b['fixed_numerals']
raw = {'J', 'f', 'r'}
expected = [[n, '+', 'n_'+n, 1] for n in a['witnesses'] if n not in raw and n != 'zeta']
rename = {n: 'n_'+n for n in raw}
for n, op, x, y in a['source']:
    if n == 'g52': continue
    if n == 'k': expected.extend([['kbase', '+', 'eta', 'n_zeta'], ['k', '+', 'kbase', 1]])
    elif n == 'r0': expected.append(['r0', '-', 'kbase', 'R'])
    else: expected.append([n, op, rename.get(x, x), rename.get(y, y)])
assert b['source'] == expected and a['operations'] == 88 and b['operations'] == len(expected) == 97
known = set(b['witnesses'] + b['fixed_numerals'])
for n, op, x, y in expected:
    assert n not in known and op in ('+', '-', '*')
    assert all(type(z) is int or z in known for z in (x, y)); known.add(n)
live = {'out'}
for n, op, x, y in reversed(expected):
    if n in live: live.update(z for z in (x,y) if isinstance(z, str))
assert all(n in live for n, _, _, _ in expected) and set(b['witnesses'] + b['fixed_numerals']) <= live
def calc(g, env, modulus):
    e = env.copy()
    for n, op, x, y in g['source']:
        x = x if type(x) is int else e[x]; y = y if type(y) is int else e[y]
        e[n] = (x+y if op == '+' else x-y if op == '-' else x*y) % modulus
    return e
rng = random.Random(138099)
for modulus in (4, 17, 1009):
    for _ in range(100):
        eb = {n: rng.randrange(-8,9) for n in b['witnesses'] + b['fixed_numerals']}
        ea = {n: eb['n_'+n] + (0 if n in raw else 1) for n in a['witnesses']}
        ea.update({n: eb[n] for n in a['fixed_numerals']})
        aa, bb = calc(a, ea, modulus), calc(b, eb, modulus)
        assert all(aa[n] == bb[n] for n in ('A0','A1','Fa','g72','out'))
# Finite root-switch controls are sanity checks, not the universal proof.
for m in range(1, 30):
    for k in range(2, 30):
        ell = m*k
        assert ell*ell < 1+ell*(ell+k) < (ell+k)*(ell+k)
p72 = D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = load(p72/'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115 = load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed = {}
for n, item in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw'] == item['sha256_raw'] and b115['ports'][n]['sha256_gzip'] == item['sha256_gzip']
    z = (p72/item['path']).read_bytes(); assert digest(z) == item['sha256_gzip']
    rawbytes = gzip.decompress(z); assert len(rawbytes) == item['raw_bytes'] and digest(rawbytes) == item['sha256_raw']
    fixed[n] = int.from_bytes(rawbytes, 'little')
assert set(fixed) == set(b['fixed_numerals']) and fixed['beta'] >= 46 and fixed['K0'] >= 0 and 0 < fixed['MC'] < fixed['beta'] and 0 < fixed['MF'] < 2*fixed['beta']
prime = 1000000007
def trim(x):
    while len(x)>1 and x[-1]==0: x.pop()
    return x
def add(x,y,s):
    return trim([((x[i] if i<len(x) else 0)+s*(y[i] if i<len(y) else 0))%prime for i in range(max(len(x),len(y)))])
def mul(x,y):
    out=[0]*(len(x)+len(y)-1)
    for i,a0 in enumerate(x):
        for j,b0 in enumerate(y):out[i+j]=(out[i+j]+a0*b0)%prime
    return trim(out)
e = {n:[0,1] for n in b['witnesses']};e.update({n:[v%prime] for n,v in fixed.items()})
def val(x):return [x%prime] if type(x) is int else e[x]
for n,op,x,y in expected:
    x,y=val(x),val(y);e[n]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
assert len(e['out'])-1 == 28 and e['out'][-1] == 59132194
print(json.dumps({'scope':'external zero-existence map only; no Lean, iPRA or PDF binding',
                  'variables':13,'operations':97,'all_gates_inputs_ports_live':True,
                  'signed_modular_identity_controls':300,'ray_degree':len(e['out'])-1,
                  'ray_leader':e['out'][-1],'ray_prime':prime},sort_keys=True,indent=2))
