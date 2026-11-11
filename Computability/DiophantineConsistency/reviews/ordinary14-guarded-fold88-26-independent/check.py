#!/usr/bin/env python3
"""Independent guarded-row, port and weighted-ray check; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-guarded-fold88-26'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
final_readme=read(A/'README.md','9829a2170bfddb7fb2befa6cfc13b3a06edbb4ffe64653fa9dbdc1afad59ec20')
link_tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary14-guarded-fold88-26-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='f8a419ba1261b8e1b47945c51f2797f0715d1c90d5033432242fb3949df8778a'
read(A/'check.py','137d2178f436bc83887a1db22d68212c33a732f7b2c7a313676e3f6fb74fa7ce')
read(A/'result.json','8a48648cac924e5ec438beaa61d17a12d2522c26e115ac86e10d513ea18c1c92')
p=json.loads(read(D/'research/ordinary13-folded-root86-negated/candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166'))
c=json.loads(read(A/'candidate.json','a3c5f7d9ed6f2c55a49818c5927f08b6293216bbecce24731a99890c83cc6ada'))
expect=[(['Z','+',r[2],r[3]] if r[0]=='g34' else r) for r in p['source'] if r[0] not in ('folded_q3Bt','Z')]
assert c['witnesses']==p['witnesses']+['t'] and c['fixed_numerals']==p['fixed_numerals'] and c['source']==expect+[['bt_quotient','*','qm','t'],['guard','-','Bt','bt_quotient'],['guard2','*','guard','guard'],['guarded_out','+','out','guard2']] and len(c['source'])==88
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
# The first norm and k>2 imply tau<ell+k/2 by an exact square difference.
for m in range(1,50):
 for k in range(3,50):assert (2*m*k+k)**2-4*(1+m*(m+1)*k*k)==k*k-4>0
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'operations':88,'variables':14,'prime':P,'weighted_ray_degree':26,'weighted_ray_leader':v['guarded_out'][-1],'arithmetic_controls':controls,'scope':'external positive-zero equivalence under beta>0, 0<=K0<(beta+1)^2; no Lean or PDF theorem'},sort_keys=True,indent=2))
