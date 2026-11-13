from pathlib import Path
from hashlib import sha256
from math import isqrt,gcd
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-f-unshift-fixed-positive-gap-norm-congruences-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('research/ordinary13-f-unshift-fixed-positive-gap-norm-congruences','reviews/ordinary13-eta85-main-ordinate-q-bound-independent'):
 p=Path(name);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta85-shift-boundary-probes/F-probe.json').read_text());r={row[0]:row[1:] for row in g['source']}
for n,row in {'q':['+',1,'qm'],'X':['*','q','n_w'],'Y':['*','q3','s'],'U':['*','Y','q2'],'qF':['-','q','n_F'],'C':['-','qF','alpha'],'k':['+','kbase',1],'Bt':['-','g27','n_F'],'Z':['-','g32','Bt'],'R':['+','g47','g50'],'r0':['-','kbase','R'],'shift':['-','g54','r0'],'Dstar':['+','g58','g59'],'A0':['-','g38','g42'],'A1':['-','g61','g65']}.items():assert r[n]==row,(n,r.get(n))
source=Path('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean').read_text()
assert 'theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)' in source
assert '2*ycoord time (2*(Q-1)+1)=k' in source
assert 'theorem even_ordinate' in source
mask=Path('Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean').read_text();assert 'range 943 ∪ Ico 983 993' in mask and '}) \\ {1}' in mask
lst=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text();assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in lst
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
# Symbolic identities for inverse first-Pell step and its positivity test.
Z=(0,0,0)
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
def var(i):
 e=[0]*3;e[i]=1;return P({tuple(e):1})
M,x,k=(var(i) for i in range(3));D0=M*(M+1);A=2*M+1
xp=A*x-2*D0*k;kp=A*k-2*x
assert xp*xp-D0*kp*kp==x*x-D0*k*k
assert A*A*k*k-4*(1+D0*k*k)==k*k-4
# Independently exercise full descent from every bounded first-Pell solution.
solutions=0
for M0 in range(1,80):
 for k0 in range(1,300):
  norm=1+M0*(M0+1)*k0*k0;x0=isqrt(norm)
  if x0*x0!=norm:continue
  x,k=x0,k0;n=0
  while k:
   xp=(2*M0+1)*x-2*M0*(M0+1)*k;kp=(2*M0+1)*k-2*x
   assert xp>0 and 0<=kp<k and xp*xp==1+M0*(M0+1)*kp*kp
   x,k=xp,kp;n+=1
  assert x==1 and k0%2==0 and (k0-2*n)%(4*M0)==0
  solutions+=1
# H odd power-of-two cancellation and parity of actual R form.
for q in (2,4,8,16,32,64):
 for s in (1,2,3):
  Y=q**3*s;H=3+4*Y;assert gcd(H,q**5)==1
 for C in range(1,q):
  for MC in range(0,q,2):
   for MF in (0,1,q,2*q-1):
    R=(q*q-C)*(q*q-1)+MC+q*MF
    assert (R-C-MC)%q==0
    if (R+1)%2==0:assert C%2==1
print(json.dumps({'author_and_q_bound_review_receipts_reproduced':True,'actual_Fzero_signed_root_rank_wiring_checked':True,'retained_positive_parameter_Pell_interface_checked':True,'inverse_Pell_polynomial_identities':True,'bounded_complete_descent_solutions':solutions,'q_power_two_cancellation_and_C_parity_controls':True,'graph_factor_extraction_or_lean_proved':False,'lean_executed':False},sort_keys=True,indent=2))
