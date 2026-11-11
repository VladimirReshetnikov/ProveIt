#!/usr/bin/env python3
"""Exact unscaling, graph liveness and compact44 degree ray; no Lean."""
import gzip,hashlib,json,random,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
def pin(p,h):raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,p;return raw
old=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'));g=json.loads(pin(P/'candidate.json','f042c821e0588409568725db3e3092ec72fb6cc3fd5713bec6819136e9d1aaba'))
assert old['witnesses']==g['witnesses'] and old['fixed_numerals']==g['fixed_numerals'] and old['output']==g['output']
assert [r[0] for r in old['source'] if 'M' in r[2:]]==['Z','g39'] and [r[0] for r in old['source'] if 'Z' in r[2:]]==['g38'] and [r[0] for r in old['source'] if 'g39' in r[2:]]==['g42'] and [r[0] for r in old['source'] if 'g42' in r[2:]]==['A0']
expected=[]
for n,op,a,b in old['source']:
 if n in ('M','Z','g39','g42'):continue
 if n=='g38':assert [n,op,a,b]==['g38','*','Z','Z'];a=b='g31'
 if n=='A0':assert [n,op,a,b]==['A0','-','g38','g42'];b='g41'
 expected.append([n,op,a,b])
assert expected==g['source'] and len(expected)==80
known=set(g['witnesses']+g['fixed_numerals']);used={g['output']}
for n,op,a,b in expected:assert n not in known and op in '+-*' and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
counts={o:sum(r[1]==o for r in expected) for o in '+-*'}
# Free polynomial identity for the exact first-residual factor.
def add(a,b,s=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+s*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(sorted(k+l));z[t]=z.get(t,0)+v*w
 return {k:v for k,v in z.items() if v}
def v(n):return {(n,):1}
M,A,B=map(v,('M','g31','g41'));new=add(mul(A,A),B,-1);oldA=add(mul(mul(M,A),mul(M,A)),mul(mul(M,M),B),-1);assert oldA==mul(mul(M,M),new)
def calc(graph,vals):
 vals=vals.copy()
 for n,op,a,b in graph['source']:
  a=a if isinstance(a,int) else vals[a];b=b if isinstance(b,int) else vals[b];vals[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return vals
rng=random.Random(0x8060)
for _ in range(80):
 vals={x:rng.randrange(-4,5) for x in g['witnesses']+g['fixed_numerals']};o=calc(old,vals);n=calc(g,vals);assert o['A0']==o['M']**2*n['A0'] and all(o[x]==n[x] for x in ('A1','Fa','g72','guard')) and o['guarded_out']-n['guarded_out']==(o['M']**4-1)*n['A0']**2
# Retain and rerun the independent corrected 84 review.
Q=D/'reviews/ordinary14-qcube84-probe-independent';pin(Q/'check.py','88f5c911e5f3840ab51d19e8c597845a068ea880ec73e8d24e214a510ec4417c');pin(Q/'result.json','7f7fabbb30be535db0bc79cd3449b261ee81786d8a9333ffba497148dc4b22b9');r=subprocess.run([sys.executable,'-I','-S','-B',str(Q/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(Q/'result.json').read_bytes()
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));C=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];raw=gzip.decompress(pin(root/m['path'],m['sha256_gzip']));assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>0
mod=1000000007;env={n:[0,1] for n in g['witnesses']};env.update({n:[x%mod] for n,x in ports.items()})
def trim(a):
 while len(a)>1 and not a[-1]:a.pop()
 return a
def pol(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for n,op,a,b in expected:env[n]=pol(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['guarded_out'])==61 and env['guarded_out'][-1]!=0
print(json.dumps({'operations':80,'operation_breakdown':counts,'all_gates_inputs_ports_live':True,'first_residual_M_squared_identity':True,'signed_integer_controls':80,'prime':mod,'ray_degree':60,'ray_leader':env['guarded_out'][-1],'scope':'pointwise positive-domain same-zero graph for beta>0; compact44 endpoint inherited externally; no Lean or PDF binding'},sort_keys=True,indent=2))
