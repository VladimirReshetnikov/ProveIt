#!/usr/bin/env python3
"""Independent 80-gate delta, pointwise factor controls and weighted ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def raw(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
old=json.loads(raw('research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
new=json.loads(raw('research/ordinary14-unscale-first80/candidate.json','f042c821e0588409568725db3e3092ec72fb6cc3fd5713bec6819136e9d1aaba'))
author=raw('research/ordinary14-unscale-first80/README.md','2e626846a5108214f9c76b67a6eb453ba29e87ff85a97a0b81ee0ce10e61b682')
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-unscale-first80-root-independent/`.\n'
assert author.endswith(tail) and hashlib.sha256(author[:-len(tail)]).hexdigest()=='c920e47bb963a18a9a954b782644d0239c4621c658e4609b67321d5c318bea85'
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
expect=[]
for r in old['source']:
 if r[0] in ('M','Z','g39','g42'):continue
 if r[0]=='g38':expect.append(['g38','*','g31','g31'])
 elif r[0]=='A0':expect.append(['A0','-','g38','g41'])
 else:expect.append(r)
assert new['source']==expect and len(new['source'])==80
for n,uses in {'M':['Z','g39'],'Z':['g38'],'g39':['g42'],'g42':['A0']}.items():assert [r[0] for r in old['source'] if n in r[2:]]==uses
known=set(new['witnesses']+new['fixed_numerals']);assert len(known)==18
for name,op,a,b in new['source']:
 assert name not in known and all(isinstance(x,int) or x in known for x in (a,b));known.add(name)
need={new['output']}
for n,op,a,b in reversed(new['source']):
 if n in need:need.update((a,b))
assert all(r[0] in need for r in new['source']) and all(x in need for x in new['witnesses']+new['fixed_numerals'])
def calc(g,v):
 v=v.copy()
 for n,op,a,b in g['source']:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b]
  v[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return v
rng=random.Random(800060)
for _ in range(160):
 v={x:rng.randint(-3,3) for x in new['witnesses']+new['fixed_numerals']};a=calc(old,v);b=calc(new,v)
 assert a['A0']==a['M']**2*b['A0']
 assert all(a[n]==b[n] for n in ('A1','Fa','g72','guard'))
 assert a['guarded_out']-b['guarded_out']==(a['M']**4-1)*b['A0']**2
p='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
bind=json.loads(raw(p+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(raw('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
fixed={}
for n,m in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(D/p/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
assert fixed['beta']>0
P=1000000009;v={n:[0,j+1] for j,n in enumerate(new['witnesses'])};v.update({n:[x%P] for n,x in fixed.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 return trim(z)
def val(x):return [x%P] if isinstance(x,int) else v[x]
for n,op,a,b in new['source']:v[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
assert len(v['guarded_out'])-1==60 and v['guarded_out'][-1]!=0
print(json.dumps({'graph_delta':'PASS','topology_and_liveness':'PASS','positive_zero_argument':'M>0, sum of integer squares','signed_controls':160,'prime':P,'weighted_ray_degree':60,'weighted_ray_leader':v['guarded_out'][-1],'scope':'external pointwise positive-zero comparison and degree; no Lean, PDF or provider replay'},sort_keys=True,indent=2))
