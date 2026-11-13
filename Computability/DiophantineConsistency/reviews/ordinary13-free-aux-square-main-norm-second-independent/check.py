from pathlib import Path
from hashlib import sha256
from math import gcd,isqrt
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-free-aux-square-main-norm-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-main-norm-nonsquare-partial')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text());r={n:(op,a,b) for n,op,a,b in g['source']}
assert g['witnesses'][11]=='n_y2'
for n,row in {'Q':('*','Delta','rho'),'I':('*','c2','i'),'g72':('-','g71','Q'),
 'V':('-','g76','c'),'g81':('-','n_y2','V2'),'Fa':('-','n_y2','g82'),
 'R':('+','g47','g50'),'Dstar':('+','g58','g59'),'A1':('-','g61','g65')}.items():assert r[n]==row
# Exact polynomial identity in z=I² and b, independent implementation.
N=2;zero=(0,0)
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0,0];e[i]=1;return {tuple(e):1}
def add(a,b,sgn=1):
 o=a.copy()
 for k,v in b.items():o[k]=o.get(k,0)+sgn*v
 return {k:v for k,v in o.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 o={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));o[k]=o.get(k,0)+v*w
 return {k:v for k,v in o.items() if v}
one=C(1);two=C(2);z,b=V(0),V(1);vm=add(one,mul(b,sub(z,one)))
y2=add(add(one,mul(two,mul(b,z))),mul(mul(b,b),mul(z,sub(z,one))))
assert mul(sub(z,one),y2)==sub(mul(z,mul(vm,vm)),one)
# Finite fields: independently count x²−y²=D and the associated character
# sum using explicit square residue sets rather than Euler exponentiation.
for p0 in (5,7,11,13,17,19,23,29,31,37,41,43,47):
 sq={x*x%p0 for x in range(p0)}
 def chi(x):return 0 if x%p0==0 else (1 if x%p0 in sq else -1)
 for delta in range(1,p0):
  assert sum(chi((x*x-delta)%p0) for x in range(p0))==-1
 for i in range(1,p0):
  z=i*i%p0;lead=z*(z-1)%p0
  if lead==0:continue
  vals=[(1+2*b*z+b*b*lead)%p0 for b in range(p0)]
  assert sum(map(chi,vals))==-chi(lead) and any(chi(x)==-1 for x in vals)
# Independent compact-like structural controls: a=0,1; choose actual matrix
# periods, derive CRT T and a character nonresidue for the free square.
def prime(x):return x>=2 and all(x%d for d in range(2,isqrt(x)+1))
controls=[]
for a0 in (0,1):
 A=a0+2;Delta=A*A-1;c=4*Delta+3;R=2*c+3;f,v=1,0
 for h in range(1,c**8+1):
  f,v=A*f+Delta*v,f+A*v
  if f%(c*c)==1 and v%(c*c)==0:break
 else:raise AssertionError('period')
 assert v>0 and v%(c*c)==0 and f*f-Delta*v*v==1
 i=Delta*(v//(c*c));I=i*c*c;assert i>0 and I==Delta*v and I*I==Delta*(f*f-1)
 p0=next(t for t in range(5,200) if prime(t) and (f*c*I*(I*I-1))%t)
 sq={x*x%p0 for x in range(p0)}
 u=next(u for u in range(p0) if (1+2*(4+f*f*c*u)*I*I+(4+f*f*c*u)**2*I*I*(I*I-1))%p0 not in sq)
 b0=4+f*f*c*u;V0=1+b0*(I*I-1);nY=1+2*b0*I*I+b0*b0*I*I*(I*I-1)
 numerator=V0+f*f*R+c;den=f*f*c
 assert V0%(f*f)==(-c)%(f*f) and (V0+f*f*R+c)%c==0 and gcd(f*f,c)==1
 assert numerator%den==0 and numerator//den>=1 and (I*I-1)*nY==I*I*V0*V0-1
 assert nY%p0 not in sq
 controls.append({'a':a0,'c':c,'period':h,'prime':p0,'u':u})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'actual_literal_fields_checked':True,
 'exact_auxiliary_polynomial_identity':True,'finite_field_character_controls':True,
 'CRT_strong_and_nonsquare_controls':controls,'natural_norm_is_actual_signed_root':False,
 'full_compact_child_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
