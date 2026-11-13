#!/usr/bin/env python3
"""direct positive Pell root and authenticated compact44 degree; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
c=load(H/'candidate.json','5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507')
p=load(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
expect=[]
for row in p['source']:
 if row[0] in ('M','g31','Z','g39','g42'):continue
 if row[0]=='g38':expect.append(['g38','*','r','r'])
 elif row[0]=='A0':expect.append(['A0','-','g38','g41'])
 else:expect.append(row)
assert c['source']==expect and len(c['source'])==79
assert len({r[0] for r in c['source']})==79 and not ({r[0] for r in c['source']} & set(c['witnesses']+c['fixed_numerals']))
needed={'guarded_out'}
for n,op,x,y in reversed(c['source']):
 if n in needed:needed.update((x,y))
assert all(r[0] in needed for r in c['source']) and all(x in needed for x in c['witnesses']+c['fixed_numerals'])
def calc(graph,vs):
 d=vs.copy()
 def val(x):return x if isinstance(x,int) else d[x]
 for n,op,x,y in graph['source']:
  a,b=val(x),val(y);d[n]=a*b if op=='*' else a+b if op=='+' else a-b
 return d
rng=random.Random(7960)
for _ in range(100):
 v={x:rng.randrange(-4,5) for x in p['witnesses']+p['fixed_numerals']};old=calc(p,v);v['r']=old['g31'];new=calc(c,v)
 assert old['A0']==old['M']**2*new['A0']
 for name in ('A1','Fa','g72','guard'):assert old[name]==new[name]
 assert old['guarded_out']-new['guarded_out']==(old['M']**4-1)*new['A0']**2
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,m in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
assert fixed['beta']==(1<<590069)-1
assert fixed['beta']>=46 and 0<=fixed['K0'] and 0<fixed['MC']<fixed['beta'] and 0<fixed['MF']<2*fixed['beta']
prime=1000000007;v={x:[0,1] for x in c['witnesses']};v.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
def val(x):return [x%prime] if isinstance(x,int) else v[x]
for n,op,x,y in c['source']:v[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(v['guarded_out'])-1==60 and v['guarded_out'][-1]!=0
print(json.dumps({'operations':79,'variables':14,'all_gates_inputs_ports_live':True,'all_integer_substitution_controls':100,'port_bounds_checked':True,'prime':prime,'ray_degree':60,'ray_leader':v['guarded_out'][-1],'scope':'external direct-root source/substitution and degree controls; positive-zero equivalence submitted for review; no Lean/PDF binding'},sort_keys=True,indent=2))
