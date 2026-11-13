from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-high-index-norm-independent');A=Path('research/ordinary13-independent-k-high-index-norm-audit')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
# Separate exact sparse polynomial identities in independent indeterminates.
Z=(0,)*5
def C(n):return {Z:n} if n else {}
def v(i):
 e=[0]*5;e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 r=a.copy()
 for k,x in b.items():r[k]=r.get(k,0)+sign*x
 return {k:x for k,x in r.items() if x}
def mul(a,b):
 r={}
 for k,x in a.items():
  for j,y in b.items():
   t=tuple(i+l for i,l in zip(k,j));r[t]=r.get(t,0)+x*y
 return {k:x for k,x in r.items() if x}
def sub(a,b):return add(a,b,-1)
A0,x,y,q,n=[v(i) for i in range(5)];D0=sub(mul(A0,A0),C(1))
xx=add(mul(A0,x),mul(D0,y));yy=add(x,mul(A0,y))
assert sub(mul(xx,xx),mul(D0,mul(yy,yy)))==sub(mul(x,x),mul(D0,mul(y,y)))
q2=mul(q,q);q3=mul(q2,q);q4=mul(q3,q)
assert sub(sub(sub(q4,q3),q),mul(C(2),n))==add(mul(sub(q,C(1)),sub(q3,C(2))),sub(sub(q,mul(C(2),n)),C(2)))
def pell(A,j):
 x,y=1,0;D=A*A-1
 for i in range(j):
  xx=A*x+D*y;yy=x+A*y
  assert xx*xx-D*yy*yy==1 and xx>=1 and yy>=i+1
  x,y=xx,yy
 return x,y
cases=0
for n0 in (14,15,19,24,31):
 for extra in (0,1,7):
  q0=2*n0+2+extra;X=q0;Y=q0**3;m=X*Y*Y;B=2*m+1
  tau,y0=pell(B,n0);k=2*y0
  assert tau*tau==1+m*(m+1)*k*k and y0>=n0 and (y0-n0)%(2*m)==0
  s=(y0-n0)//(2*m);assert s>=0 and k==2*n0+4*m*s
  R=2*n0-1;mu=q0**4
  assert R>=26 and (2*n0)%mu==R+1 and R+q0**3+q0+1<=mu
  L=(Y+1)*k+1
  assert L-Y*k==k+1 and L>n0
  cases+=1
# Independent index-convention source anchors: first Pell base is A-2,
# main base is a, so ycoord(0,b)=0 and ycoord(1,b)=1.
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for x in ['def delta (b : V) : V := (b+1)*(b+3)','run 0 b=⟪1,0⟫','xcoord (time+1) b=(b+2)*xcoord time b+delta b*ycoord time b','ycoord (time+1) b=xcoord time b+(b+2)*ycoord time b']:
 assert x in rec,x
for m in range(1,30):assert ((2*m-1)+2)==2*m+1 and (2*m)*(2*m+2)==4*m*(m+1)
source=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();assert 'def betaNat : ℕ := 2^(67*8807)-1' in source
print(json.dumps({'author_receipt_reproduces':True,'formal_norm_step_and_window_identities':True,'finite_high_first_index_cases':cases,'index_parameter_conventions_checked':True,'actual_graph_rank_or_roots_bound':False,'full_graph_zero_proved':False,'lean_executed':False},sort_keys=True,indent=2))
