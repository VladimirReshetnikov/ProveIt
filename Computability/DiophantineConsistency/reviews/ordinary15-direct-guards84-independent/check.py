#!/usr/bin/env python3
"""Independent auxiliary-root graph delta, positive-bound controls and weighted ray."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def raw(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
old=json.loads(raw('research/ordinary13-aux-root87-36/candidate.json','abdd93cebd85dc2194478a76297d16ea04ca06855265420abf0b6c1b7e70db51'))
new=json.loads(raw('research/ordinary15-direct-guards84/candidate.json','a4304844c9860ac1468d9cdbb4b75dd8d18c177ab5db267a24658cbdbce0fb43'))
author=raw('research/ordinary15-direct-guards84/README.md','42c5f6e8c1db049e39a3b7e67718f4c05b45adc740f13aad93b151b831159e4b')
tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary15-direct-guards84-independent/`.\n'
assert author.endswith(tail) and hashlib.sha256(author[:-len(tail)]).hexdigest()=='e2aa2f6e442197442bedcfc2fc6e8c55e3c04660a03a13efa7e3340ff706d20a'
assert new['witnesses']==old['witnesses']+['s_guard','t_guard'] and old['fixed_numerals']==new['fixed_numerals']
expect=[]
for r in old['source']:
 if r[0] in ('M','g31','folded_kBt','folded_g31','g32','g33','g34','folded_q3Bt','Z','g39','g42'):continue
 if r[0]=='g38':expect.append(['g38','*','r','r'])
 elif r[0]=='A0':expect.append(['A0','-','g38','g41'])
 else:expect.append(r)
expect += [['Y_expected','*','q3','s_guard'],['guard_y','-','Y','Y_expected'],['guard_y2','*','guard_y','guard_y'],['partial_out','+','out','guard_y2'],['Bt_expected','*','qm','t_guard'],['guard_bt','-','Bt','Bt_expected'],['guard_bt2','*','guard_bt','guard_bt'],['guarded_out','+','partial_out','guard_bt2']]
assert new['source']==expect and len(new['source'])==84
known=set(new['witnesses']+new['fixed_numerals']);assert len(known)==19
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
rng=random.Random(841536)
for _ in range(160):
 v={x:rng.randint(-3,3) for x in new['witnesses']+new['fixed_numerals']};n=calc(new,v)
 ov={x:v[x] for x in old['witnesses']+old['fixed_numerals']}
 ov['r']=n['k']*n['Bt']-n['ell']-n['k']-v['s_guard']+v['t_guard']+v['r'];o=calc(old,ov)
 M=n['q3']*n['qm']
 assert o['Z']==M*v['r']+n['qm']*n['guard_y']-n['q3']*n['guard_bt']
 assert all(o[z]==n[z] for z in ('A1','Fa','g72'))
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
assert len(v['guarded_out'])-1==36 and v['guarded_out'][-1]!=0
print(json.dumps({'graph_delta':'PASS','topology_and_liveness':'PASS','positive_zero_argument':'positive quotient guards and Pell descent give positive parent root','signed_controls':160,'prime':P,'weighted_ray_degree':36,'weighted_ray_leader':v['guarded_out'][-1],'scope':'external two-quotient positive-zero comparison and degree; no Lean, PDF or provider replay'},sort_keys=True,indent=2))
