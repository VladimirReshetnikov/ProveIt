#!/usr/bin/env python3
"""Independent auxiliary-root graph delta, positive-bound controls and weighted ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def raw(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
old=json.loads(raw('research/ordinary14-direct-pell79/candidate.json','5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'))
new=json.loads(raw('research/ordinary14-aux-root78/candidate.json','d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43'))
readme=raw('research/ordinary14-aux-root78/README.md','461164edefa8b442580c9d186fa1bf1ade7f4d128c9cbc70bbb112f1af52d938')
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-aux-root78-math-independent/`.\n'
assert readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='68bcc75baae9290ec00545a1aee53d6147536bfb997787a3db87419354a14a2c'
assert new['witnesses']==['y' if x=='u' else x for x in old['witnesses']] and old['fixed_numerals']==new['fixed_numerals']
expect=[]
for r in old['source']:
 if r[0] in ('g78','g80'):continue
 if r[0]=='y2':expect.extend([['y2','*','y','y'],['V2','*','V','V']])
 elif r[0]=='g81':expect.append(['g81','-','y2','V2'])
 else:expect.append(r)
assert new['source']==expect and len(new['source'])==78
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
rng=random.Random(7860)
for _ in range(160):
 v={x:rng.randint(-3,3) for x in old['witnesses']+old['fixed_numerals']};a=calc(old,v);v['y']=a['V']+v['u'];b=calc(new,v)
 assert all(a[n]==b[n] for n in ('A0','A1','Fa','g72','guard','guarded_out'))
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
assert len(v['guarded_out'])-1==60 and v['guarded_out'][-1]!=0
print(json.dumps({'graph_delta':'PASS','topology_and_liveness':'PASS','positive_zero_argument':'Pell and strong norms give |V|>1, hence |y|>|V|','signed_controls':160,'prime':P,'weighted_ray_degree':60,'weighted_ray_leader':v['guarded_out'][-1],'scope':'external auxiliary-coordinate positive-zero comparison and degree; no Lean, PDF or provider replay'},sort_keys=True,indent=2))
