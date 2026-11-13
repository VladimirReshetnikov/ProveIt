from pathlib import Path
from hashlib import sha256
import json,sys,subprocess,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-main-norm-nonsquare-partial')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-free-aux-square-compact-factor-obstruction','ordinary13-free-square-compact-factor-obstruction'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
for n,row in {'Q':['*','Delta','rho'],'I':['*','c2','i'],'g72':['-','g71','Q'],'V':['-','g76','c'],'g81':['-','n_y2','V2'],'Fa':['-','n_y2','g82'],'R':['+','g47','g50'],'Dstar':['+','g58','g59']}.items():assert r[n]==row,(n,r.get(n))
# Exact auxiliary polynomial identity in t=I² and b=auxiliary coefficient.
Z=(0,0)
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P(r)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({Z:x})
t=P({(1,0):1});b=P({(0,1):1});V=1+b*(t-1);y2=1+2*b*t+b*b*t*(t-1)
assert (t-1)*y2==t*V*V-1
# Independent finite-field character-sum controls for nondegenerate
# quadratic in b: sum chi(P(b))=-chi(leading coefficient).
character_controls=0
for p in (5,7,11,13,17,19,23,29,31):
 for I in range(1,p):
  t0=I*I%p;lead=t0*(t0-1)%p
  if not lead:continue
  def chi(x):
   x%=p
   if not x:return 0
   return 1 if pow(x,(p-1)//2,p)==1 else -1
  vals=[chi(1+2*b*t0+b*b*lead) for b in range(p)]
  assert sum(vals)==-chi(lead) and -1 in vals
  character_controls+=1
# Fully evaluated noncompact toy with a genuine even matrix period.
def pell(A,n):
 d=A*A-1;x,y=1,0;u,v=A,1
 while n:
  if n&1:x,y=x*u+d*y*v,x*v+y*u
  u,v=u*u+d*v*v,2*u*v;n//=2
 return x,y
q=2;beta=1;Y=q**3;X=0;a=Y;A=a+2;delta=A*A-1;c=4*delta+3;R=402;alpha=133
assert R%c==3 and R==(alpha+beta*beta)*(q*q-1)
x,y=1,0
for h in range(1,10000):
 x,y=(A*x+delta*y)%(c*c),(x+A*y)%(c*c)
 if (x,y)==(1,0) and h%2==0:break
else:raise AssertionError('toy even period')
f,v=pell(A,h);I=delta*v;assert v%(c*c)==0 and math.gcd(f,A)==1 and f*f==1+delta*v*v
product=f*c*I*(I*I-1)
def prime(p):return p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
p=next(p for p in range(5,200) if prime(p) and product%p)
for u in range(p):
 b=4+f*f*c*u;t=I*I;z=1+2*b*t+b*b*t*(t-1)
 if pow(z%p,(p-1)//2,p)==p-1:break
else:raise AssertionError('toy nonresidue search')
V=1+b*(I*I-1);num=V+f*f*R+c;den=f*f*c
assert num%den==0;T=num//den;i=I//(c*c)
assert T>=1 and i>0 and V==f*f*(T*c-R)-c
k,eta=divmod(c,Y);zeta=k-eta;assert zeta>=0
vals=[1,0,alpha-1,f,i-1,T-1,0,0,0,eta,zeta,z,0];ports=[beta,0,0,0]
d=dict(zip(g['witnesses'],vals));d.update(zip(g['fixed_numerals'],ports))
for n,op,x,y in g['source']:
 x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
 d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
g3,c3=pell(A,3)
assert c3==c and g3*g3==1+delta*c*c
assert d['R']==R and d['c']==c and d['I']==I and d['V']==V and d['g72']==0 and d['Fa']==1
assert d['A0']!=0 and d['A1']!=0 and pow(z%p,(p-1)//2,p)==p-1
print(json.dumps({'two_predecessor_receipts_reproduced':True,'auxiliary_polynomial_identity_exact':True,'finite_field_character_controls':character_controls,'toy_q':q,'toy_even_period':h,'toy_prime':p,'toy_u':u,'toy_free_y2_bits':z.bit_length(),'toy_natural_main_norm_and_actual_strong_aux':True,'toy_actual_first_main_residuals_nonzero':True,'fixed_compact_full_zero_claim':False,'lean_executed':False},sort_keys=True,indent=2))
