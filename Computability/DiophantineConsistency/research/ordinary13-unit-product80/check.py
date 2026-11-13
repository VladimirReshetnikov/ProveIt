#!/usr/bin/env python3
"""Unit-product graph, modular exclusions, integer controls and degree ray."""
import gzip, hashlib, itertools, json, random
from pathlib import Path
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
def load(path,sha):
    data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==sha
    return json.loads(data)
c=load(H/'candidate.json','449adf0f03f08cbb73b4ca8c823cb88b79111243c93705b5404f89d18568a22b')
p=load(D/'research/ordinary13-residue-first81/candidate.json','067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
gone={'A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out'}
expected=[row for row in p['source'] if row[0] not in gone]
expected += [['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]
assert c['source']==expected and len(expected)==80
known=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in expected:
    assert op in ('+','-','*') and n not in known
    assert all(isinstance(z,int) or z in known for z in (x,y)); known.add(n)
needed={'out'}
for n,op,x,y in reversed(expected):
    if n in needed: needed.update((x,y))
assert all(row[0] in needed for row in expected)
assert all(x in needed for x in c['witnesses']+c['fixed_numerals'])
for b,x,s,k,z in itertools.product(range(4),repeat=5):
    q=b+1; Y=q**3*s; ell=x*Y*Y*k
    F0=1+z*z-b*b*(1+ell*(ell+k))
    assert F0%4!=3
for a,U,c0,d in itertools.product(range(4),repeat=4):
    delta=a*a+4*a+3
    F1=1+d*d-U*U*(1+delta*c0*c0)
    assert F1%4!=3
for a,f,i,c0,y,V in itertools.product(range(4),repeat=6):
    delta=a*a+4*a+3; Q=delta*(f*f-1); I=i*c0*c0
    Fa=y*y-Q*(y*y-V*V); Fs=1+I*I-Q
    assert Fa%4!=3 and Fs%4!=3
def calc(graph,env):
    d=env.copy()
    def val(x): return x if isinstance(x,int) else d[x]
    for n,op,x,y in graph['source']:
        a,b=val(x),val(y); d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d
rng=random.Random(1380106)
for _ in range(160):
    env={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']}
    old=calc(p,env); new=calc(c,env)
    for n in ('A0','A1','Fa','g72'): assert old[n]==new[n]
    assert all(new[n]%4!=3 for n in ('F0','F1','Fa','Fs'))
    assert (old['out']==0)==(new['out']==0)
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed={}
for n,m in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
    z=(p72/m['path']).read_bytes(); assert hashlib.sha256(z).hexdigest()==m['sha256_gzip']
    raw=gzip.decompress(z); assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
prime=1000000007
env={x:[0,1] for x in c['witnesses']};env.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sign):return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
    return trim(z)
def val(x):return [x%prime] if isinstance(x,int) else env[x]
for n,op,x,y in expected:env[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(env['out'])-1==99 and env['out'][-1]!=0
print(json.dumps({'operations':80,'variables':13,'all_gates_inputs_ports_live':True,'mod4_controls_pass':True,'signed_controls':160,
    'prime':prime,'ray_degree':len(env['out'])-1,'ray_leader':env['out'][-1],
    'scope':'external graph and finite controls; unit proof and degree require independent review; no Lean/PDF binding'},sort_keys=True,indent=2))
