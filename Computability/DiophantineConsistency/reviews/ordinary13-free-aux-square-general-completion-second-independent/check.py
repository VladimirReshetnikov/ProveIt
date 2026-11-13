from pathlib import Path
from hashlib import sha256
from math import gcd,isqrt
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-free-aux-square-general-completion-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-general-nonsquare-completion')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Independently trace every row's input dependencies for both the author's
# eta/zeta-natural probe and the exact shifted-zeta parent alternative.
changed={'n_f','n_i','n_T','n_y2'};observations={}
for name in ('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json',
 'research/ordinary13-shifted85-free-aux-square-criterion/candidate.json'):
 g=json.loads(Path(name).read_text());d={n:{n} for n in g['witnesses']+g['fixed_numerals']}
 r={n:(op,a,b) for n,op,a,b in g['source']}
 for n,op,a,b in g['source']:d[n]=(d[a] if isinstance(a,str) else set())|(d[b] if isinstance(b,str) else set())
 for field in ('A0','A1','a','c','R','X','Y','U','Dstar'):
  assert not(d[field]&changed),(name,field,d[field]&changed)
 for n,row in {'f2':('*','n_f','n_f'),'rho':('-','f2',1),'Q':('*','Delta','rho'),
  'I':('*','c2','i'),'g72':('-','g71','Q'),'V':('-','g76','c'),
  'g81':('-','n_y2','V2'),'Fa':('-','n_y2','g82')}.items():assert r[n]==row
 observations[name]={'rows':len(g['source']),'first_main_and_context_unchanged':True}
# Exact auxiliary identity in z=I² and b as sparse integer polynomials.
zero=(0,0)
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0,0];e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 r={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,0)+v*w
 return {k:v for k,v in r.items() if v}
one=C(1);two=C(2);z,b=V(0),V(1);VV=add(one,mul(b,sub(z,one)))
YY=add(add(one,mul(two,mul(b,z))),mul(mul(b,b),mul(z,sub(z,one))))
assert mul(sub(z,one),YY)==sub(mul(z,mul(VV,VV)),one)
def isprime(p):return p>=2 and all(p%d for d in range(2,isqrt(p)+1))
def pell(A,n):
 Delta=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+Delta*y,x+A*y
 return x,y
controls=[]
for a,c,R in ((0,1,-100),(1,2,-1000),(2,3,7),(3,4,-25),(4,5,3)):
 A=a+2;Delta=A*A-1;x,y=1,0
 for h in range(1,2*c**8+1):
  x,y=(A*x+Delta*y)%(c*c),(x+A*y)%(c*c)
  if h%2==0 and (x,y)==(1%(c*c),0):break
 else:raise AssertionError((a,c))
 f,v=pell(A,h);assert v>0 and v%(c*c)==0 and f*f-Delta*v*v==1 and gcd(A,f)==gcd(f*f,c)==1
 i=Delta*(v//(c*c));I=c*c*i;assert i>0 and I>1 and I*I==Delta*(f*f-1)
 fm=f*f;bf=((1+c)*pow(A*A,-1,fm))%fm
 b0=bf+fm*(((R+1-bf)*pow(fm,-1,c))%c)
 assert (b0*A*A-(1+c))%fm==0 and (b0-R-1)%c==0
 prime=next(p for p in range(5,300) if isprime(p) and (f*c*I*(I*I-1))%p)
 sq={x*x%prime for x in range(prime)}
 u=next(u for u in range(prime) if (1+2*(b0+fm*c*u)*I*I+(b0+fm*c*u)**2*I*I*(I*I-1))%prime not in sq)
 b0+=fm*c*u;V0=1+b0*(I*I-1);num=V0+fm*R+c;den=fm*c
 assert num%den==0
 if num//den<1:
  extra=(1-num//den+prime*(I*I-1)-1)//(prime*(I*I-1))
  b0+=fm*c*prime*extra;V0=1+b0*(I*I-1);num=V0+fm*R+c
 T=num//den;y2=1+2*b0*I*I+b0*b0*I*I*(I*I-1)
 assert T>=1 and i>=1 and V0==fm*(T*c-R)-c and (I*I-1)*y2==I*I*V0*V0-1 and y2%prime not in sq
 controls.append({'a':a,'c':c,'rank':R,'period':h,'prime':prime,'T_positive':True})
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'independent_graph_dependency_observations':observations,
 'exact_auxiliary_polynomial_identity':True,'Pell_CRT_nonsquare_controls':controls,
 'R_negative_controls_included':True,'full_zero_existence_proved':False,
 'lean_executed':False},sort_keys=True,indent=2))
