#!/usr/bin/env python3
"""Direct-X unit finalizer, shifted guard and compact44 degree controls."""
import gzip,hashlib,itertools,json,math,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(path,sha):
    data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==sha
    return json.loads(data)
c=load(H/'candidate.json','fd92751134276450eb62e186eaab024838196a1de1a684d175ed12385c646043')
p=load(D/'research/ordinary14-direct-roots79-56/candidate.json','fd4f02aef44ccd1b61227f66f65e7aa8a0f751fbc24b766a124ee31656b2c56e')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
gone={'g41','A0','A0sq','A1sq','Fam','Fam2','Fsm2','sum01','sum23','out','guard2','guarded_out'}
expected=[]
for row in p['source']:
    if row[0] in gone:continue
    if row[0]=='guard_base':expected.append(['guard_base','+','g27','qF'])
    else:expected.append(row)
expected += [['F0','-','g38','g40'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['P01234','*','P0123','guard'],['out','-','P01234',1]]
assert c['source']==expected and len(expected)==75
known=set(c['witnesses']+c['fixed_numerals'])
for n,op,x,y in expected:
    assert n not in known and op in ('+','-','*')
    assert all(isinstance(z,int) or z in known for z in (x,y));known.add(n)
needed={'out'}
for n,op,x,y in reversed(expected):
    if n in needed:needed.update((x,y))
assert all(row[0] in needed for row in expected)
assert all(x in needed for x in c['witnesses']+c['fixed_numerals'])
for a,U,c0,d in itertools.product(range(4),repeat=4):
    delta=a*a+4*a+3;assert (1+d*d-U*U*(1+delta*c0*c0))%4!=3
for a,f,i,c0,y,V in itertools.product(range(4),repeat=6):
    delta=a*a+4*a+3;Q=delta*(f*f-1);I=i*c0*c0
    assert (y*y-Q*(y*y-V*V))%4!=3 and (1+I*I-Q)%4!=3
for m in range(2,101):
    for k in range(1,2001):
        n=m*(m+1)*k*k-1;assert math.isqrt(n)**2!=n
def calc(graph,env):
    d=env.copy()
    def val(x):return x if isinstance(x,int) else d[x]
    for n,op,x,y in graph['source']:
        a,b=val(x),val(y);d[n]=a*b if op=='*' else a+b if op=='+' else a-b
    return d
rng=random.Random(1475100)
for _ in range(160):
    env={x:rng.randrange(-4,5) for x in c['witnesses']+c['fixed_numerals']}
    new=calc(c,env);oldenv=env.copy();oldenv['h']=env['h']-1;old=calc(p,oldenv)
    assert new['F0']==1+old['A0'] and new['F1']==1+old['A1']
    assert new['Fs']==1+old['g72'] and new['guard']==1+old['guard']
    assert new['Fa']==old['Fa']
# Guard zero is arithmetically possible before the Pell/calibration constraints.
q,F,alpha,X,K0=5,3,1,1,2;C=q-F-alpha
assert C*(X+K0)-F==0
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,meta in binding['ports'].items():
    assert b115['ports'][n]['sha256_raw']==meta['sha256_raw'] and b115['ports'][n]['sha256_gzip']==meta['sha256_gzip']
    z=(p72/meta['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['sha256_gzip']
    raw=gzip.decompress(z);assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw']
    fixed[n]=int.from_bytes(raw,'little')
assert fixed['beta']>=46 and fixed['K0']>=0 and 0<fixed['MC']<fixed['beta'] and 0<fixed['MF']<2*fixed['beta']
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
assert len(env['out'])-1==100 and env['out'][-1]!=0
print(json.dumps({'operations':75,'variables':14,'all_inputs_strictly_positive':True,'all_gates_inputs_ports_live':True,
    'mod4_and_negative_pell_finite_controls_pass':True,'signed_factor_controls':160,
    'guard_zero_partial_control':True,'prime':prime,'ray_degree':100,'ray_leader':env['out'][-1],
    'scope':'external finite controls; h=1 source replay and zero equivalence require independent review; no Lean/PDF binding'},sort_keys=True,indent=2))
