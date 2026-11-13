from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize
D=Path('reviews/current2011-shear-aux-leading-obstruction-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/current2011-shear-aux-leading-obstruction')
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],check=True,stdout=subprocess.PIPE,timeout=30).stdout==(A/'result.json').read_bytes()
g=json.loads(Path('research/current2011-sheared72-46-candidate/polynomial.json').read_text())
def add(a,b,s=1):
 z=[0]*max(len(a),len(b))
 for i,x in enumerate(a):z[i]+=x
 for i,x in enumerate(b):z[i]+=s*x
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def ray(vals,ports):
 e={n:[0,x] for n,x in zip(g['witnesses'],vals)};e.update({n:[x] for n,x in zip(g['fixed_numerals'],ports)})
 for name,op,a,b in g['source']:
  a=[a] if isinstance(a,int) else e[a];b=[b] if isinstance(b,int) else e[b]
  e[name]=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
 return e
def coeff(xs,n):return xs[n] if n<len(xs) else 0
rng=random.Random(724623)
for _ in range(80):
 v=[rng.randrange(-2,3) for _ in range(14)];p=[rng.choice([-3,-2,-1,1,2,3]),rng.randrange(-2,3),rng.randrange(-2,3),rng.randrange(-2,3)];e=ray(v,p)
 J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma=v;beta=p[0];q0=beta*J;k=eta+zeta;Y=s*q0**3;E=w*s*q0**4;W=w*(q0-F-alpha)-z*q0
 assert coeff(e['N0'],22)==-E**2*k**2*Y**2 and len(e['N0'])<=23
 assert coeff(e['strong_residual'],22)==i**2*k**4*Y**4 and len(e['strong_residual'])<=23
 assert coeff(e['rQW'],20)==8*gamma*E**2*k*Y*W and len(e['rQW'])<=21
 assert coeff(e['Na'],23)==-2*E**2*f**4*k*Y*T*y and len(e['Na'])<=24
 assert coeff(e['polynomial'],46)==coeff(e['Na'],23)**2 and len(e['polynomial'])<=47
for k in range(-4,5):
 v=[1]*14;v[5]=0;v[10]=k;v[11]=0;v[13]=0;e=ray(v,[1,2,3,4])
 assert coeff(e['N0'],22)==-k*k and coeff(e['Na'],23)==-2*k
 assert coeff(e['strong_residual'],22)==coeff(e['rQW'],20)==0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'author_exact_symbolic_check_reproduced':True,'full_graph_symbolic_ray_controls':80,'k_specialization_controls':9,'learned_polynomial_scope':'bounded multiplier degrees only','lean_executed':False},sort_keys=True,indent=2))
