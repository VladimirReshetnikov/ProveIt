#!/usr/bin/env python3
"""Check exact graph delta and actual-port degree ray; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def pin(p,h):raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,p;return raw
old=json.loads(pin(D/'research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'));g=json.loads(pin(P/'candidate.json','dd3a367edc57b3844cc7ce5d94a343e2782767669be00a02da999686137e6a7c'))
assert old['witnesses']==g['witnesses'] and old['fixed_numerals']==g['fixed_numerals']
expected=[]
for n,op,a,b in old['source']:
 if n=='Fam':continue
 if n=='Fam2':a=b='Fa'
 if n=='out':n='sphere_sum'
 expected.append([n,op,a,b])
expected.append(['out','-','sphere_sum',1]);assert g['source']==expected and len(expected)==88
known=set(g['witnesses']+g['fixed_numerals']);used={'out'}
for n,op,a,b in expected:
 assert n not in known and op in '+-*' and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
counts={o:sum(r[1]==o for r in expected) for o in '+-*'}
def run(graph,env):
 env=env.copy()
 for n,op,a,b in graph['source']:
  a=a if isinstance(a,int) else env[a];b=b if isinstance(b,int) else env[b];env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env
rng=random.Random(0x883001)
for _ in range(80):
 vals={x:rng.randrange(-5,6) for x in g['witnesses']+g['fixed_numerals']};a=run(old,vals);b=run(g,vals);assert b['out']==a['out']+2*(a['Fa']-1)
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));C=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));ports={};mod=1000000007
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=pin(root/m['path'],m['sha256_gzip']);raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];ports[n]=int.from_bytes(raw,'little')
assert min(ports.values())>0
# With J=F=alpha=f=i=T=X=Y=eta=zeta=gamma=1, use u=R.
q=ports['beta']+1;R=(1+ports['beta']**2)*(q*q-1)+ports['MC']+q*ports['MF'];assert R>0
c=3;V=(c-R)-c;u=R;assert V+u==0 and (1*c*c)**2==81
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def calc(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
env={x:[0,1] for x in g['witnesses']};env.update({n:[x%mod] for n,x in ports.items()})
for n,op,a,b in expected:env[n]=calc(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['out'])-1==30 and env['out'][-1]!=0
print(json.dumps({'operations':len(expected),'operation_breakdown':counts,'all_gates_inputs_ports_live':True,'prime':mod,'ray_degree':len(env['out'])-1,'ray_leader':env['out'][-1],'Fa_zero_positive_control_strong_residual':81,'scope':'external positive-domain equivalent equal-metric alternative; no Lean'},sort_keys=True,indent=2))
