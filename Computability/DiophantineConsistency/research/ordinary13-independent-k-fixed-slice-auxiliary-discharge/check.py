from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-fixed-slice-auxiliary-discharge')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
for name in ['ordinary13-independent-k-fixed-slice-conditional','ordinary13-independent-k-actual-rank-boundary-audit']:
 p=Path('research')/name
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Polynomial identities for the odd-index Chebyshev induction, in variables
# A,P_j,P_(j+1). Equality is over Z[A,P,Q], not tested by sampling.
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
    key=tuple(x+y for x,y in zip(k,j));r[key]=r.get(key,0)+v*w
  return P(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,P) else P({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
A,prev,cur=(var(i) for i in range(N));t=1-A*A
assert 4*t-3==-(4*A*A-1)
assert (4*t-2)*(-cur)-prev==(4*A*A-2)*cur-prev
# Constant-term recurrence: P_l(0)=(-1)^l(2l+1).
for l in range(20):
 a=(-1)**l*(2*l+1);b=(-1)**(l+1)*(2*l+3)
 assert -2*b-a==(-1)**(l+2)*(2*l+5)
# Compact low-mask unit digit: base rho divisible by 4, index 0 belongs
# to support but is not the special index, hence MC≡rho-2≡2 mod 4.
mask=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993' in mask and '}) \\ {1}' in mask
assert 0 in ((set(range(943))|{1063,1064,1095,2195,3296})-{1}) and 0!=1063
assert (2**67-2)%4==2 and (2**(67%2))%3==2
# q≡0, G≡−1, q²−1≡−1, MC≡2 imply R≡3 mod4.
assert ((-1)*(-1)+2)%4==3
# Small exact Pell/CRT controls, avoiding all fixed huge constants.
def pell(A0,n):
 x,y=1,0;D0=A0*A0-1
 for _ in range(n):x,y=A0*x+D0*y,x+A0*y
 return x,y
tests=[]
for a,R,h in [(0,3,90),(1,3,210),(2,3,378)]:
 A0=a+2;Delta=A0*A0-1;g,c=pell(A0,R);f,v=pell(A0,h)
 assert h>0 and v>0 and f>=1 and v%(c*c)==0
 i=Delta*(v//(c*c));I=i*c*c
 assert i>0 and I>1 and I*I==Delta*(f*f-1)
 x,y=pell(I,R);assert x%I==0;V=x//I
 assert V>0 and V% (f*f)==(-c)%(f*f) and V%c==(-R)%c
 numerator=V+f*f*R+c;denominator=f*f*c
 assert numerator%denominator==0;T=numerator//denominator
 assert T>=1 and V==f*f*(T*c-R)-c
 assert y*y-I*I*(y*y-V*V)==1
 tests.append({'a':a,'R':R,'period_h':h,'c':c,'positive_T':True})
print(json.dumps({'exact_odd_chebyshev_initial_and_step_identities':True,'constant_term_recurrence_checked':True,'fixed_rank_is_3_mod_4':True,'finite_strong_period_controls':tests,'positive_auxiliary_T_and_factor_checked':True,'remaining_main_condition':'H divides 2^R-q','main_condition_decided':False,'huge_fixed_values_materialized':False,'lean_executed':False},sort_keys=True,indent=2))
