from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixed-slice-auxiliary-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-fixed-slice-auxiliary-discharge')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
assert 'range 943 ∪ Ico 983 993' in Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text()
assert (2**67-2)%4==2 and (67*8807)%2==1 and pow(2,67*8807,3)==2
assert ((-1)*(-1)+2)%4==3
# Explicit polynomial coefficient lists independently check P_l identities.
def trim(p):
 while len(p)>1 and p[-1]==0:p.pop()
 return p
def scale(p,c):return trim([c*x for x in p])
def sub(a,b):return trim([(a[i] if i<len(a) else 0)-(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return trim(o)
def compose(p,v):
 out=[0]
 for coefficient in reversed(p):
  out=mul(out,v);out[0]+=coefficient
 return trim(out)
P0=[1];P1=[-3,4];Q0=[1];Q1=[-1,0,4]
for l in range(20):
 assert compose(P0,[1,0,-1])==scale(Q0,(-1)**l)
 assert P0[0]==(-1)**l*(2*l+1)
 P0,P1=P1,sub(mul([-2,4],P1),P0)
 Q0,Q1=Q1,sub(mul([-2,0,4],Q1),Q0)
# Small constructive controls include modulus-c² matrix period, exact CRT,
# positivity of i,f,V,T, and both residual equations.
def pell(A,n):
 x,y=1,0;delta=A*A-1
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
controls=0
for a in range(1,3):
 A=a+2;delta=A*A-1
 for R in (3,):
  g,c=pell(A,R);f,v=1,0
  for h in range(1,c**8+1):
   f,v=A*f+delta*v,f+A*v
   if f%(c*c)==1 and v%(c*c)==0:break
  else:raise AssertionError('period')
  i=delta*(v//(c*c));I=i*c*c
  assert v>0 and f>1 and i>0 and I>1 and I*I==delta*(f*f-1)
  x,y=pell(I,R);assert x%I==0;V=x//I
  assert V% (f*f)==(-c)%(f*f) and V%c==(-R)%c
  numerator=V+f*f*R+c;den=f*f*c
  assert numerator%den==0;T=numerator//den
  assert T>=1 and V==f*f*(T*c-R)-c and y*y-I*I*(y*y-V*V)==1
  controls+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'odd_polynomial_coefficient_controls':20,
 'fixed_rank_phase_and_mod3_checked':True,'constructive_Pell_CRT_controls':controls,
 'main_divisibility_undecided':True,'lean_executed':False},sort_keys=True,indent=2))
