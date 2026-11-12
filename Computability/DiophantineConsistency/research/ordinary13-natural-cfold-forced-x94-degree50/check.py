#!/usr/bin/env python3
"""External graph/degree checks for the 13-input forced-coordinate natural candidate; no Lean."""
from pathlib import Path
import gzip, hashlib, json, random, math
P = Path(__file__).resolve().parent
D = P.parents[1]
def digest(b): return hashlib.sha256(b).hexdigest()
def load(path, sha):
    b = path.read_bytes(); assert digest(b) == sha, str(path); return json.loads(b)
a = load(D/'research/ordinary13-natural-cfold-forced-gamma95-degree50/candidate.json', '732e96e5d7278fb08357910e5f9b4aad2a248bc8e86c7ec89328bbf20039a889')
b = load(P/'candidate.json', '07eefb9e44f827bbb6b613903fc7b1a7b08bcf1d9685517628a7cdb754cee535')
assert b['parent_sha256'] == digest((D/'research/ordinary13-natural-cfold-forced-gamma95-degree50/candidate.json').read_bytes())
assert a['domain'] == b['domain'] == 'nonnegative integers'
assert b['witnesses'] == a['witnesses'] and a['fixed_numerals'] == b['fixed_numerals']
assert ['X', '+', 'n_X', 1] in a['source']
expected = [[n,op,'n_X' if x=='X' else x,'n_X' if y=='X' else y] for n,op,x,y in a['source'] if n!='X']
assert b['source'] == expected and a['operations'] == 95 and b['operations'] == len(expected) == 94
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
        ea = eb.copy();ea['n_X'] -= 1
        aa, bb = calc(a, ea, modulus), calc(b, eb, modulus)
        assert all(aa[n] == bb[n] for n in ('F0','F1','Fa','Fs','out'))
# Finite root-switch controls are sanity checks, not the universal proof.
for q in range(2,8):
    for s in range(1,4):
        Y=q**3*s;H=4*Y+3;U=Y*q*q;c=2*(Y+2);d=2*(Y+2)**2-1
        assert d*d-(Y*Y+H)*c*c==1 and H>3*q*q
        assert math.gcd(H,d-Y*c)==math.gcd(H,-d-Y*c)==1
        assert (U*(d-Y*c))%H!=0 and (U*(-d-Y*c))%H!=0
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
assert len(e['out'])-1 == 50 and e['out'][-1] == 604845992
print(json.dumps({'scope':'external zero-existence map only; no Lean, iPRA or PDF binding',
                  'variables':13,'operations':94,'all_gates_inputs_ports_live':True,
                  'signed_modular_identity_controls':300,'divisibility_sanity_controls':18,'ray_degree':len(e['out'])-1,
                  'ray_leader':e['out'][-1],'ray_prime':prime},sort_keys=True,indent=2))
