#!/usr/bin/env python3
"""Independent source, mod-4 and weighted-ray controls; no Lean."""
import gzip,hashlib,json,itertools,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary13-freej88-conditional-sphere'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
final_readme=read(A/'README.md','73caccdbd54d2c1666f81ca4936a99d1f43601852d216709d56058dcbfbf1695')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-freej88-conditional-sphere-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='0799766a8947c2cde2e2da59c03be3a27d0cb9f512d13e10e87a6f55debbb037'
read(A/'check.py','06ef6e533b4f78495fd2e21c0315cce6d2bd6e987362ce476bf741a8ea66b3fb');read(A/'result.json','055aa7a286f1194af76c1e9388dbdf3cbfce383c8d98706d6051cc410f1460dd')
old=json.loads(read(D/'research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'));g=json.loads(read(A/'candidate.json','dd3a367edc57b3844cc7ce5d94a343e2782767669be00a02da999686137e6a7c'))
rows=[]
for n,op,a,b in old['source']:
 if n=='Fam':continue
 if n=='Fam2':a=b='Fa'
 if n=='out':n='sphere_sum'
 rows.append([n,op,a,b])
rows.append(['out','-','sphere_sum',1]);assert rows==g['source'] and len(rows)==88
needed={'out'}
for n,op,a,b in reversed(rows):
 if n in needed:needed.update((a,b))
assert all(r[0] in needed for r in rows) and all(n in needed for n in g['witnesses']+g['fixed_numerals'])
for a,f,y,V in itertools.product(range(4),repeat=4):
 delta=(a*a+4*a+3)%4;Q=(delta*(f*f-1))%4;Fa=(y*y-Q*(y*y-V*V))%4;assert Q in (0,1) and Fa!=3
for Q in range(2,60):
 for y in range(-35,36):
  for V in range(-35,36):
   if y and V:assert (Q-1)*y*y!=Q*V*V
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bind=json.loads(read(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));b115=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));P=1000000007;fixed={}
for n,m in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=read(p72/m['path'],m['sha256_gzip']);raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(raw,'little')%P
v={n:[0,j+1] for j,n in enumerate(g['witnesses'])};v.update({n:[x] for n,x in fixed.items()})
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
for n,op,a,b in rows:v[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
assert len(v['out'])==31 and v['out'][-1]!=0
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'operations':88,'prime':P,'weighted_ray_degree':30,'weighted_ray_leader':v['out'][-1],'scope':'external positive-domain same-zero equal-metric alternative; no Lean or global lower bound'},sort_keys=True,indent=2))
