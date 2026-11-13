#!/usr/bin/env python3
"""Direct-qF graph, actual-port scalar seed and modular degree ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(path,sha):
    data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==sha
    return json.loads(data)
c=load(H/'candidate.json','734b2467ac242178e5d44285a573e27430748555927b0eb7121316066e2796ce')
p=load(D/'research/ordinary14-positive-guard74/candidate.json','e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')
assert c['witnesses']==['qF' if x=='F' else x for x in p['witnesses']]
assert c['fixed_numerals']==p['fixed_numerals']
expected=[row for row in p['source'] if row[0]!='qF']
assert c['source']==expected and len(expected)==73
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
rng=random.Random(1473107)
for _ in range(160):
    env={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']}
    new=calc(c,env);old_env={x:env[x] for x in p['witnesses'] if x!='F'}
    old_env.update({x:env[x] for x in p['fixed_numerals']});old_env['F']=new['q']-env['qF']
    old=calc(p,old_env)
    for n in ('qF','C','G','R','A1','Fa','g72','F0','F1','Fs','guard','out'):assert new[n]==old[n]
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,meta in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==meta['sha256_raw'] and b115['ports'][n]['sha256_gzip']==meta['sha256_gzip']
    z=(p72/meta['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['sha256_gzip']
    raw=gzip.decompress(z);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
B=590069;b=fixed['beta'];q=b+1;assert b==2**B-1 and fixed['K0']>=0
A=b*q*(q*q-1);G0=3*b*q+1-2*b;R0=G0*(q*q-1)+fixed['MC']+q*fixed['MF']
L=R0.bit_length()+1;S=A.bit_length()+1;t=2+(1<<L)+(1<<(L+S))
qF=q+b*t;alpha=1+b*(t-2);C=qF-alpha;G=b*qF+alpha
R=G*(q*q-1)+fixed['MC']+q*fixed['MF']
assert C==3*b and q-qF==-b*t<0 and qF>0 and alpha>0
assert R==R0+(A<<L)+(A<<(L+S)) and R%4==3
assert A.bit_count()==2*B and R.bit_length()==7080832
assert ((R-1)//2).bit_count()==3540414 and ((R-1)//2).bit_count()>=3*B+1
assert R>2*B and 0<R0.bit_length()<L and A.bit_length()<S
def sha_int(n):return hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'little')).hexdigest()
prime=1000000007;env={x:[0,i+2] for i,x in enumerate(c['witnesses'])};env.update({n:[x%prime] for n,x in fixed.items()})
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
print(json.dumps({'operations':73,'variables':14,'all_inputs_strictly_positive':True,'all_gates_inputs_ports_live':True,
    'signed_shift_controls':160,'B':B,'rank_bits':R.bit_length(),'rank_mod4':R%4,
    'N_popcount':((R-1)//2).bit_count(),'rank_sha256_little_endian':sha_int(R),
    'prime':prime,'ray_degree':len(env['out'])-1,'ray_leader':env['out'][-1],
    'scope':'external graph and finite seed controls; full symbolic zero and degree bound require independent review; no Lean/PDF binding'},sort_keys=True,indent=2))
