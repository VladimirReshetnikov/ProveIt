#!/usr/bin/env python3
"""External graph/degree checks for the 14-input forced-gamma natural candidate; no Lean."""
from pathlib import Path
import gzip, hashlib, json, random
P = Path(__file__).resolve().parent
D = P.parents[1]
def digest(b): return hashlib.sha256(b).hexdigest()
def load(path, sha):
    b = path.read_bytes(); assert digest(b) == sha, str(path); return json.loads(b)
a = load(D/'research/ordinary14-natural-forcedj81/candidate.json', '24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999')
b = load(P/'candidate.json', '136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5')
assert b['parent_sha256'] == digest((D/'research/ordinary14-natural-forcedj81/candidate.json').read_bytes())
assert a['domain'] == b['domain'] == 'nonnegative integers'
assert b['witnesses'] == a['witnesses'] and a['fixed_numerals'] == b['fixed_numerals']
assert ['gamma', '+', 'n_gamma', 1] in a['source']
expected = [[n,op,'n_gamma' if x=='gamma' else x,'n_gamma' if y=='gamma' else y] for n,op,x,y in a['source'] if n!='gamma']
assert b['source'] == expected and a['operations'] == 81 and b['operations'] == len(expected) == 80
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
rng = random.Random(138088)
for modulus in (4, 17, 1009):
    for _ in range(100):
        eb = {n: rng.randrange(-8,9) for n in b['witnesses'] + b['fixed_numerals']}
        ea = eb.copy();ea['n_gamma'] -= 1
        aa, bb = calc(a, ea, modulus), calc(b, eb, modulus)
        assert all(aa[n] == bb[n] for n in ('F0','F1','Fa','Fs','out'))
# Finite root-switch controls are sanity checks, not the universal proof.
for m in range(1, 30):
    for k in range(2, 30):
        ell = m*k
        assert ell*ell < 1+ell*(ell+k) < (ell+k)*(ell+k)
# Sanity controls for the unbounded orientation inequalities, not a proof.
for q in range(2,8):
    for w in range(1,4):
        for s in range(1,4):
            X=q*w;Y=q**3*s;m=X*Y*Y;k=8*m+4;R=q**4-1
            a=X*Y+Y;c=1+Y*k;H=3+4*a;U=Y*q*q
            assert k>R+1 and c>X and Y*Y*q*q*a>H
            assert U*(X+a*c)+H*(R+1-k)>0
p72 = D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = load(p72/'ACTIVE_BINDING.json', '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115 = load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json', 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed = {}
for n, item in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw'] == item['sha256_raw'] and b115['ports'][n]['sha256_gzip'] == item['sha256_gzip']
    z = (p72/item['path']).read_bytes(); assert digest(z) == item['sha256_gzip']
    rawbytes = gzip.decompress(z); assert len(rawbytes) == item['raw_bytes'] and digest(rawbytes) == item['sha256_raw']
    fixed[n] = int.from_bytes(rawbytes, 'little')
assert set(fixed) == set(b['fixed_numerals']) and fixed['beta'] >= 46 and fixed['K0'] > 0 and 0 < fixed['MC'] < fixed['beta'] and 0 < fixed['MF'] < 2*fixed['beta']
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
assert len(e['out'])-1 == 107 and e['out'][-1] == 419359493
print(json.dumps({'scope':'external zero-existence map only; no Lean, iPRA or PDF binding',
                  'variables':14,'operations':80,'all_gates_inputs_ports_live':True,
                  'signed_modular_identity_controls':300,'ray_degree':len(e['out'])-1,
                  'ray_leader':e['out'][-1],'ray_prime':prime},sort_keys=True,indent=2))
