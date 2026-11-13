from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-explicit-pell-period-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
source=Path('Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean').read_text()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
draft=(D/'ExplicitPellPeriod.lean.src').read_text()
for t in ['theorem doubled_quotients (n R a : V)', 'xcoord (2*n*R) a=1+ycoord R a*ycoord R a*r', 'ycoord (2*n*R) a=2*n*xcoord R a*ycoord R a+ycoord R a*ycoord R a*s', 'theorem squared_ordinate (R a : V)']:assert t in source,t
for t in ['def delta (b : V) : V := (b+1)*(b+3)','(b+2)*π₁ previous+delta b*π₂ previous','π₁ previous+(b+2)*π₂ previous']:assert t in rec,t
for t in ['doubled_quotients (ycoord m a) m a','2*xcoord m a+s','2*m*ycoord m a = 2*ycoord m a*m','#print axioms']:assert t in draft,t
# Independent coefficient map: 2*c*d*c + c*c*s = (2*d+s)*c*c.
c={(1,0,0):1};d={(0,1,0):1};s={(0,0,1):1}
def add(x,y):
 z=x.copy()
 for e,v in y.items():z[e]=z.get(e,0)+v
 return {e:v for e,v in z.items() if v}
def mul(x,y):
 z={}
 for e,v in x.items():
  for f,w in y.items():
   k=tuple(a+b for a,b in zip(e,f));z[k]=z.get(k,0)+v*w
 return {e:v for e,v in z.items() if v}
def scale(n,x):return {e:n*v for e,v in x.items()}
assert add(scale(2,mul(mul(c,d),c)),mul(mul(c,c),s))==mul(mul(add(scale(2,d),s),c),c)
def mm(a,b,p):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%p for i in range(2) for j in range(2))
def mpow(Q,n,p):
 z=(1,0,0,1)
 while n:
  if n&1:z=mm(z,Q,p)
  Q=mm(Q,Q,p);n//=2
 return z
count=0
for a in range(7):
 A=a+2;delta=(a+1)*(a+3);x,c=1,0
 for m in range(1,9):
  x,c=A*x+delta*c,x+A*c
  Q=(A,delta,1,A);h=2*m*c;v=mpow(Q,h,c*c)
  assert v[0]==1%(c*c) and v[2]==0
  count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'existing_doubled_quotients_interface_checked':True,'coefficient_identity_checked':True,'bounded_matrix_controls':count,'draft_elaborated':False,'lean_executed':False,'ipra_internal_proof_constructed':False},sort_keys=True,indent=2))
