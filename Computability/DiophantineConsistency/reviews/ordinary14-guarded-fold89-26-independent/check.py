#!/usr/bin/env python3
"""Independent guarded-row, port and weighted-ray check; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-guarded-fold89-26'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
final_readme=read(A/'README.md','1f3f262e784aba1d39666a72955436af0c4335c4953f17cc8e38be997b2cbd0f')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-guarded-fold89-26-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='97560962fbbc54b14d4387a6bde3c42e413a935a5aeed0d40cb15e42e73ee975'
read(A/'check.py','896e85d2f3c68e5ede2117d5c677b2e447aa889dcd395c9c65226f08eb598530')
read(A/'result.json','dbf1f0bd20a218438dd9cc80bb90abae12bbd7be436a0e9bc052da291ee8ba0e')
p=json.loads(read(D/'research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166'))
c=json.loads(read(A/'candidate.json','4f0758dd44c61c72c7ac19b244336306bcb588f600debe6b4dbdb686916a6012'))
assert c['witnesses']==p['witnesses']+['h'] and c['fixed_numerals']==p['fixed_numerals'] and c['source']==p['source']+[['guard','-','Bt','h'],['guard2','*','guard','guard'],['guarded_out','+','out','guard2']] and len(c['source'])==89
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
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'operations':89,'variables':14,'prime':P,'weighted_ray_degree':26,'weighted_ray_leader':v['guarded_out'][-1],'arithmetic_controls':controls,'scope':'external positive-zero equivalence under beta>0, 0<=K0<(beta+1)^2; no Lean or PDF theorem'},sort_keys=True,indent=2))
