from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-high-index-norm-audit')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Sparse integer polynomial identities in variables A,x,y,m,q,n.
N=6;z=(0,)*N
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
def pol(x):return x if isinstance(x,P) else P({z:x})
def v(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
A,x,y,m,q,n=(v(i) for i in range(N));Delta=A*A-1
xp=A*x+Delta*y;yp=x+A*y
assert xp*xp-Delta*yp*yp==x*x-Delta*y*y
assert (2*m+1)*(2*m+1)-1==4*m*(m+1)
assert q*q*q*(q-1)-q-2*n==(q-1)*(q*q*q-2)+(q-2*n-2)
# Bounded arithmetic controls never iterate the huge chosen main index.
def pell(A,j):
 x,y=1,0;delta=A*A-1
 for _ in range(j):x,y=A*x+delta*y,x+A*y
 return x,y
cases=0
for n0 in [14,15,20,25]:
 for q0 in [2*n0+2,2*n0+5]:
  X=q0;Y=q0**3;m0=X*Y*Y;firstA=2*m0+1
  tau,y0=pell(firstA,n0);k=2*y0
  assert tau*tau==1+m0*(m0+1)*k*k and y0>=n0
  assert (y0-n0)%(2*m0)==0;s=(y0-n0)//(2*m0)
  assert s>=0 and k==2*n0+4*m0*s
  R=2*n0-1;mu=q0**4
  assert R>=26 and R+q0**3+q0+1<=mu and (2*n0)%mu==R+1
  L=(Y+1)*k+1;assert L>n0 and L-Y*k>k
  cases+=1
for a in range(1,6):
 for j in range(10):
  g,c=pell(a+2,j);assert g*g==1+((a+2)**2-1)*c*c and c>=j
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
assert 'def delta (b : V) : V := (b+1)*(b+3)' in rec
assert 'xcoord time b+(b+2)*ycoord time b' in rec
print(json.dumps({'exact_pell_norm_step_identity':True,'exact_first_discriminant_identity':True,'exact_scalar_window_gap_identity':True,'arbitrary_first_index_bound':'n>=14, q>=2*n+2','compact_q_supports':'all n in 14..floor((q-2)/2)','bounded_first_index_controls':cases,'main_recurrence_inductive_controls':50,'large_main_index_iterated':False,'actual_graph_rank_root_strong_aux_claim':False,'lean_executed':False},sort_keys=True,indent=2))
