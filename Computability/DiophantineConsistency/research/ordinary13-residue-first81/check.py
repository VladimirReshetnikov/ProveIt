#!/usr/bin/env python3
"""Verify the exact source delta, signed root shift and compact44 degree ray."""
import gzip, hashlib, json, random
from pathlib import Path
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
def load(path, sha):
    data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==sha
    return json.loads(data)
c=load(H/'candidate.json','067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352')
p=load(D/'research/ordinary13-qcube-main83/candidate.json','d19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
expected=[]
for row in p['source']:
    n,op,x,y=row
    if n in ('g25','g28'): continue
    if n=='g26': expected.append(['g26','+','X','K0'])
    elif n=='Bt': expected.append(['Bt','-','g27','F'])
    else: expected.append(row)
assert c['source']==expected and len(expected)==81
assert len({r[0] for r in expected})==81
known=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in expected:
    assert op in ('+','-','*') and n not in known
    assert all(isinstance(z,int) or z in known for z in (x,y)); known.add(n)
needed={'out'}
for n,op,x,y in reversed(expected):
    if n in needed: needed.update((x,y))
assert all(r[0] in needed for r in expected)
assert all(x in needed for x in c['witnesses']+c['fixed_numerals'])
def calc(graph, env):
    d=env.copy()
    def val(x): return x if isinstance(x,int) else d[x]
    for n,op,x,y in graph['source']:
        a,b=val(x),val(y); d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d
rng=random.Random(138160)
for _ in range(160):
    env={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']}
    new=calc(c,env); old_env=env.copy()
    D0=new['C']*env['K0']-env['F']
    old_env['r']=env['r']+(new['k']*new['qm']+1)*D0
    old=calc(p,old_env)
    assert old['Bt']==new['Bt']+new['qm']*D0
    for name in ('Z','A0','A1','Fa','g72','out'): assert old[name]==new[name]
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
fixed={}
for n,m in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
    z=(p72/m['path']).read_bytes(); assert hashlib.sha256(z).hexdigest()==m['sha256_gzip']
    raw=gzip.decompress(z); assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
B=590069
assert fixed['beta']==2**B-1 and fixed['beta']>=46 and 0<=fixed['K0']
assert 0<fixed['MC']<fixed['beta'] and 0<fixed['MF']<2*fixed['beta']
prime=1000000007
env={x:[0,1] for x in c['witnesses']}; env.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a
def add(a,b,sign): return trim([((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): z[i+j]=(z[i+j]+x*y)%prime
    return trim(z)
def val(x): return [x%prime] if isinstance(x,int) else env[x]
for n,op,x,y in expected: env[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(env['out'])-1==60 and env['out'][-1]!=0
print(json.dumps({'operations':81,'variables':13,'all_gates_inputs_ports_live':True,'signed_substitution_controls':160,
    'actual_mersenne_and_port_bounds_checked':True,'prime':prime,'ray_degree':60,'ray_leader':env['out'][-1],
    'scope':'external source and finite controls; equivalence and degree bound require independent review; no Lean/PDF binding'},sort_keys=True,indent=2))
