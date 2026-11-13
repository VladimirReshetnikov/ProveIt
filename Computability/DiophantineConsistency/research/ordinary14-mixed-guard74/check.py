#!/usr/bin/env python3
"""Exact F-shift source identity and authenticated compact44 degree ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(path,sha):
    data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==sha
    return json.loads(data)
c=load(H/'candidate.json','bbb7c75f9a14df45c11e21ebcf28687f8abd6c97a773df151365a0ac71298152')
p=load(D/'research/ordinary14-negative-pell75/candidate.json','89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
assert c['domain']=='F nonnegative; all other inputs strictly positive'
expected=[]
for row in p['source']:
    n,op,x,y=row
    if n=='Fg':continue
    if n=='qF':expected.append(['qF','-','qm','F'])
    elif n=='P01234':expected.append(['P01234','*','P0123','guard'])
    else:expected.append(row)
assert c['source']==expected and len(expected)==74
known=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in expected:
    assert n not in known and op in ('+','-','*')
    assert all(isinstance(z,int) or z in known for z in (x,y));known.add(n)
needed={'out'}
for n,op,x,y in reversed(expected):
    if n in needed:needed.update((x,y))
assert all(row[0] in needed for row in expected)
assert all(x in needed for x in c['witnesses']+c['fixed_numerals'])
def calc(graph,env):
    d=env.copy()
    def val(x):return x if isinstance(x,int) else d[x]
    for n,op,x,y in graph['source']:
        a,b=val(x),val(y);d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d
rng=random.Random(1474107)
for _ in range(160):
    env={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']}
    new=calc(c,env);old_env=env.copy();old_env['F']=env['F']+1;old=calc(p,old_env)
    for n in ('qF','C','G','R','A1','Fa','g72','F0','F1','Fs','out'):assert new[n]==old[n]
    assert new['guard']==old['Fg']
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,m in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
    z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip']
    raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
assert fixed['beta']>0
prime=1000000007;env={x:[0,1] for x in c['witnesses']};env.update({n:[x%prime] for n,x in fixed.items()})
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
assert len(env['out'])-1==107 and env['out'][-1]!=0
print(json.dumps({'operations':74,'variables':14,'nonnegative_inputs':['F'],'other_inputs_strictly_positive':True,
    'all_gates_inputs_ports_live':True,'signed_shift_controls':160,'prime':prime,'ray_degree':107,'ray_leader':env['out'][-1],
    'scope':'external mixed-domain coordinate identity; independent review required; no Lean/PDF binding'},sort_keys=True,indent=2))
