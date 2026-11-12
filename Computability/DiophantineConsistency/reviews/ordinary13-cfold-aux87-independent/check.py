#!/usr/bin/env python3
"""Independent auxiliary-root graph delta, positive-bound controls and weighted ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def raw(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
old=json.loads(raw('research/ordinary13-cfold88-28/candidate.json','9497efb00c1059897dd6d57522267af90910224f2d37f8901b99dfc28086e333'))
new=json.loads(raw('research/ordinary13-cfold-aux87/candidate.json','9f63285ebcd37884064d204ce296ed03662d62d9cb9c881dd68de0a150e54f1a'))
author=raw('research/ordinary13-cfold-aux87/README.md','a08437437d11d80ba6af931ca1a29111e251888152cb3ac6088d7ba3d2918dce')
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-cfold-aux87-independent/`.\n'
assert author.endswith(tail) and hashlib.sha256(author[:-len(tail)]).hexdigest()=='38c39f61542a3f4ed9f38cabcbf20bb39be3f16a32d54f76281711e564ece000'
assert new['witnesses']==['y' if x=='u' else x for x in old['witnesses']] and old['fixed_numerals']==new['fixed_numerals']
expect=[]
for r in old['source']:
 if r[0] in ('g78','g80'):continue
 if r[0]=='y2':expect.extend([['y2','*','y','y'],['V2','*','V','V']])
 elif r[0]=='g81':expect.append(['g81','-','y2','V2'])
 else:expect.append(r)
assert new['source']==expect and len(new['source'])==87
known=set(new['witnesses']+new['fixed_numerals']);assert len(known)==17
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
rng=random.Random(7860)
for _ in range(160):
 v={x:rng.randint(-3,3) for x in old['witnesses']+old['fixed_numerals']};a=calc(old,v);v['y']=a['V']+v['u'];b=calc(new,v)
 assert all(a[n]==b[n] for n in ('Z','A0','A1','Fa','g72','out'))
for X in range(1,10):
 for Y in range(1,10):
  m=X*Y*Y;k=8*m+4;c=1+k*Y;Delta=(Y*(X+1)+2)**2-1
  assert Delta<c**3
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
assert len(v['out'])-1==36 and v['out'][-1]!=0
print(json.dumps({'graph_delta':'PASS','topology_and_liveness':'PASS','positive_zero_argument':'Pell and strong norms give |V|>1, hence |y|>|V|','signed_controls':160,'prime':P,'weighted_ray_degree':36,'weighted_ray_leader':v['out'][-1],'scope':'external auxiliary-coordinate positive-zero comparison and degree; no Lean, PDF or provider replay'},sort_keys=True,indent=2))
