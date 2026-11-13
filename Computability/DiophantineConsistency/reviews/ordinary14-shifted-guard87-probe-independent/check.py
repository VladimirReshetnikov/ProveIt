#!/usr/bin/env python3
"""Independent guarded-row, port and weighted-ray check; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-shifted-guard87-probe'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
final_readme=read(A/'README.md','9a437fdf3869679be3b4f26a3ccdd6ef87bc2ad017ea77ee43dfda8481d679f9')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-shifted-guard87-probe-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='ff44153fbd017c8028f8667848efc7208b9c1dfc9226d55ba3a50730f233a303'
read(A/'check.py','dd1835911c5731f3cc46a7582aa711e21b6500b9400a58a6920c65441508728f')
read(A/'result.json','c966e9cb636b9fa895a53ebe903fc3cdfaf82257b29c4fc453b4a9b1aadc28c0')
p=json.loads(read(D/'research/ordinary14-guarded-fold88-26/candidate.json','a3c5f7d9ed6f2c55a49818c5927f08b6293216bbecce24731a99890c83cc6ada'))
c=json.loads(read(A/'candidate.json','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'))
expect=[]
for row in p['source']:
 if row[0]=='g28':expect.append(['guard_base','-','g27','F'])
 elif row[0]=='Bt':continue
 elif row[0]=='bt_quotient':expect.append(['bt_quotient','*','qm','omega'])
 elif row[0]=='guard':expect.append(['guard','-','guard_base','bt_quotient'])
 else:expect.append(row)
assert c['witnesses']==p['witnesses'][:-1]+['omega'] and c['fixed_numerals']==p['fixed_numerals'] and c['source']==expect and len(expect)==87
needed={'guarded_out'}
for n,op,a,b in reversed(c['source']):
 if n in needed:needed.update((a,b))
assert all(r[0] in needed for r in c['source']) and all(n in needed for n in c['witnesses']+c['fixed_numerals'])
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';ports=json.loads(read(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));b115=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));fixed={}
for n,m in ports['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=read(p72/m['path'],m['sha256_gzip']);x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
assert fixed['beta']>0 and 0<=fixed['K0']<(fixed['beta']+1)**2
# Independent nonuniform ray.
P=1000000007;v={n:[0,j+1] for j,n in enumerate(c['witnesses'])};v.update({n:[x%P] for n,x in fixed.items()})
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 return trim(z)
def val(x):return [x%P] if isinstance(x,int) else v[x]
for n,op,a,b in c['source']:v[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
assert len(v['guarded_out'])==27 and v['guarded_out'][-1]!=0 and len(v['guard2'])<=5
controls=0
for b in range(1,10):
 q=b+1
 for F in range(1,q):
  for alpha in range(1,q):
   C=q-F-alpha
   for X in range(1,7):
    for K in range(min(q*q,9)):
     Bt=C*(X+K*q)-F*q
     if Bt>0 and Bt%b==0:
      t=Bt//b;Y=q**3;ell=2*X*Y*Y
      assert C>0 and F<b and alpha<b and t<X+K*q<X+q**3<ell
      controls+=1
assert controls>0
# Independent finite checks for the first two partial Pell seeds.
for Y in range(8,100):
 m=Y*Y; pell_base=2*Y+2
 for k,tau,sig in [(2,2*m+1,2),(8*m+4,8*m*m+8*m+1,4*m+4)]:
  assert tau*tau==1+m*(m+1)*k*k and m*k+k-sig+1==tau
 k=8*m+4; p3=4*pell_base*pell_base-1; p4=8*pell_base**3-4*pell_base
 assert k*Y-p3==8*Y**3-16*Y*Y-28*Y-15>0
 assert p4-k*(Y+1)==(Y+1)*(56*Y*Y+128*Y+52)>0
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'operations':87,'variables':14,'prime':P,'weighted_ray_degree':26,'weighted_ray_leader':v['guarded_out'][-1],'arithmetic_controls':controls,'scope':'shifted 87-gate probe, reverse existence open; no Lean or PDF theorem'},sort_keys=True,indent=2))
