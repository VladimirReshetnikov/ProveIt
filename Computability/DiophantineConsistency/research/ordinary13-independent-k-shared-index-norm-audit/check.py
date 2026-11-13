from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-shared-index-norm-audit')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
# Exact Pell-step certificate in independent integer-polynomial variables.
N=3;zero=(0,)*N
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
def pol(x):return x if isinstance(x,P) else P({zero:x})
def v(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
A,x,y=(v(i) for i in range(N));D0=A*A-1;xn=A*x+D0*y;yn=x+A*y
assert xn*xn-D0*yn*yn==x*x-D0*y*y
assert A*yn-xn==y
assert 4**5>4*6**3
# Small exact controls: unlike the fixed compact value, these stay tiny.
def pell(A0,n):
 x,y=1,0;D1=A0*A0-1
 for _ in range(n):x,y=A0*x+D1*y,x+A0*y
 return x,y
count=0
for n0 in (14,15,20,25):
 for q in (2*n0+2,2*n0+5):
  X=q;Y=q**3;M=X*Y*Y;a=X*Y+Y;R=2*n0-1;mu=q**4
  tau,y1=pell(2*M+1,n0);k=2*y1;g,c=pell(a+2,R);eta=c-Y*k
  assert tau*tau==1+M*(M+1)*k*k and g*g==1+(3+4*a+a*a)*c*c
  assert (y1-n0)%(2*M)==0 and y1>=n0
  s=(y1-n0)//(2*M);assert k==2*n0+4*M*s
  assert 13<=n0<R and R>=26 and R+q**3+q+1<=mu
  assert R+1<mu and (2*n0)%mu==R+1
  assert eta>k and c==eta+Y*k
  count+=1
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
assert 'def delta (b : V) : V := (b+1)*(b+3)' in rec
assert 'xcoord time b+(b+2)*ycoord time b' in rec
print(json.dumps({'pell_norm_and_growth_step_polynomial_identities':True,'shared_index_construction':'n>=14, q>=2*n+2, R=2*n-1','symbolic_growth_comparison':'q^(n-4)>4*6^(n-1) for q>=24,n>=9','bounded_exact_controls':count,'compact_q_used_symbolically_only':True,'actual_graph_rank_or_signed_root_bound':False,'strong_or_auxiliary_constraint_bound':False,'lean_executed':False},sort_keys=True,indent=2))
