#!/usr/bin/env python3
"""Bounded independent review of a natural shifted-Pell graph."""
import gzip
import hashlib
import json
import math
from pathlib import Path

D = Path(__file__).resolve().parents[2]
def sha(b): return hashlib.sha256(b).hexdigest()
def load(path, digest):
    b = path.read_bytes()
    assert sha(b) == digest
    return json.loads(b)

p = load(D / 'research/ordinary14-root74-natural-forced82/candidate.json',
         '1532ea5ec5f8dee349353044b9618a2e8a633f618e6f7ef5f1d19630b53b6c8a')
c = load(D / 'research/ordinary14-natural-shifted-pell83/candidate.json',
         '36c910fe9a6c59eeab8bfd97583dae3c27d7680f848046ed84622d9d8dd45d19')
positive = load(D / 'research/ordinary14-shifted-pell75/candidate.json',
                'cf9c2af177038c65618f351e0112c9adb21ac3726af7c83e52f7dac4224b52be')
old = {n:[op,x,y] for n,op,x,y in p['source']}
new = {n:[op,x,y] for n,op,x,y in c['source']}
assert len(old) == 82 and len(new) == 83
removed, added = {'g30','g38','g40','F0'}, {'t2','twot','twot_minus_k','ell_times','F0'}
assert set(old)-removed == set(new)-added
assert all(old[n] == new[n] for n in set(old)-removed)
assert {n:old[n] for n in removed} == {
    'g30':['+','ell','k'], 'g38':['*','n_r','n_r'],
    'g40':['*','ell','g30'], 'F0':['-','g38','g40']}
assert {n:new[n] for n in added} == {
    't2':['*','n_t','n_t'], 'twot':['*',2,'n_t'],
    'twot_minus_k':['-','twot','k'], 'ell_times':['*','ell','twot_minus_k'],
    'F0':['+','t2','ell_times']}
assert all('n_r' not in (x,y) for n,_,x,y in p['source'] if n not in removed)
assert c['domain'] == p['domain'] == 'nonnegative integers'
assert c['witnesses'] == ['n_t' if x == 'n_r' else x for x in p['witnesses']]
assert c['fixed_numerals'] == p['fixed_numerals'] and len(c['witnesses']) == 14

known = set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in c['source']:
    assert n not in known and op in ('+','-','*')
    assert all(isinstance(z,int) or z in known for z in (x,y))
    known.add(n)
live = {'out'}
for n,op,x,y in reversed(c['source']):
    if n in live: live.update(z for z in (x,y) if isinstance(z,str))
assert set(c['witnesses']+c['fixed_numerals']) <= live
assert all(n in live for n, *_ in c['source'])

# Verify a complete structural relation to the positive 75 graph, after input
# shifts and aliases. The explicitly listed cuts are justified below in the
# accompanying review; all other graph rows coincide after renaming.
pp = {n:[op,x,y] for n,op,x,y in positive['source']}
inputs = {'f':'n_f','t':'n_t','y':'n_y', 'two_t':'twot',
          'difference':'twot_minus_k','ell_product':'ell_times'}
special = {'qF','k','r0','guard_base','bt_quotient'}
for n,row in pp.items():
    if n == 'g52' or n in special: continue
    target = inputs.get(n,n)
    assert target in new, (n,target)
    op,x,y = row
    assert new[target] == [op,inputs.get(x,x),inputs.get(y,y)], n
assert {n:new[n] for n in ('J','alpha','i','T','w','s','eta','gamma')} == {
    n:['+', 'n_'+n, 1] for n in ('J','alpha','i','T','w','s','eta','gamma')}
assert pp['qF'] == ['-','q','F'] and new['qF'] == ['-','qm','n_F']
assert pp['k'] == ['+','eta','zeta'] and new['kbase'] == ['+','eta','n_zeta']
assert new['k'] == ['+','kbase',1] and pp['g52'] == ['-','k','R']
assert pp['r0'] == ['-','g52',1] and new['r0'] == ['-','kbase','R']
assert pp['guard_base'] == ['+','g27','qF'] and new['guard_base'] == ['-','g27','n_F']
assert pp['bt_quotient'] == ['*','qm','h'] and new['bt_quotient'] == ['*','qm','n_h']
assert pp['guard'] == new['guard'] == ['-','guard_base','bt_quotient']
assert pp['q'] == new['q'] == ['+',1,'qm']

# Exact sparse polynomial identities for the shifted Pell factor and the
# three structural cancellation cuts. Variables stand for arbitrary integers.
def C(n): return {():n} if n else {}
def V(s): return {(s,):1}
def A(a,b):
    z=dict(a)
    for k,v in b.items(): z[k]=z.get(k,0)+v
    return {k:v for k,v in z.items() if v}
def N(a): return {k:-v for k,v in a.items()}
def S(a,b): return A(a,N(b))
def M(a,b):
    z={}
    for x,vx in a.items():
        for y,vy in b.items():
            k=tuple(sorted(x+y)); z[k]=z.get(k,0)+vx*vy
    return {k:v for k,v in z.items() if v}
ell,k,t,b,f,g,h,eta,zeta,R=map(V,('ell','k','t','b','f','g','h','eta','zeta','R'))
assert S(M(A(ell,t),A(ell,t)),M(ell,A(ell,k))) == A(M(t,t),M(ell,S(M(C(2),t),k)))
assert S(A(C(1),b),A(f,C(1))) == S(b,f)
assert S(S(A(eta,A(zeta,C(1))),R),C(1)) == S(A(eta,zeta),R)
assert S(A(g,S(b,f)),M(b,A(h,C(1)))) == S(S(g,f),M(b,h))

# Independently reconstruct the leading ray coefficient from finite
# differences. The exact graph relation above inherits the independently
# reviewed degree-97 upper bound of the positive graph.
root = D / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding = load(root / 'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
sync = load(D / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json',
            'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,meta in binding['ports'].items():
    assert sync['ports'][n]['sha256_gzip'] == meta['sha256_gzip']
    assert sync['ports'][n]['sha256_raw'] == meta['sha256_raw']
    data=(root/meta['path']).read_bytes(); assert sha(data)==meta['sha256_gzip']
    raw=gzip.decompress(data); assert len(raw)==meta['raw_bytes'] and sha(raw)==meta['sha256_raw']
    ports[n]=int.from_bytes(raw,'little')
assert set(ports)==set(c['fixed_numerals']) and ports['beta']>0 and ports['K0']>=0
prime=1000000007
def evaluate(x):
    env={n:x for n in c['witnesses']}; env['n_t']=2*x
    env.update({n:v%prime for n,v in ports.items()})
    def val(z): return z if isinstance(z,int) else env[z]
    for n,op,a,b in c['source']:
        a,b=val(a),val(b)
        env[n]=(a*b if op=='*' else a+b if op=='+' else a-b)%prime
    return env['out']
row=[evaluate(x) for x in range(98)]
for _ in range(97): row=[(y-x)%prime for x,y in zip(row,row[1:])]
leader=row[0]*pow(math.factorial(97),-1,prime)%prime
assert leader==979034495
print(json.dumps({'external_scope':'natural-zero bijection and specialized degree; no Lean, iPRA or PDF binding',
                  'parent_gates':82,'candidate_gates':83,'witnesses':14,
                  'positive75_relation':'exact graph comparison with formal cancellation identities',
                  'degree_upper':97,'ray_degree':97,'ray_leader':leader,'prime':prime,
                  'ray_method':'97th finite difference'},indent=2,sort_keys=True))
