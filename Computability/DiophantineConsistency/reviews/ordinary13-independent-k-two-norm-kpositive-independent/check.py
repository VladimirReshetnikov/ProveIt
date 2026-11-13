from pathlib import Path
from hashlib import sha256
from math import gcd
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-two-norm-kpositive-independent')
for path,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(path).read_bytes()).hexdigest()==h,path
P=Path('research/ordinary13-independent-k-two-norm-kpositive-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
F=Path('research/ordinary13-independent-k-exceptional-kzero-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(F/'check.py')])==(F/'receipt.json').read_bytes()
# Independent polynomial normalizations for the two rank-factor bounds.
N=5;zero=(0,)*N
class P0:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=poly(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return P0(r)
 __radd__=__add__
 def __neg__(self):return P0({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-poly(o)
 def __rsub__(self,o):return poly(o)+-self
 def __mul__(self,o):
  o=poly(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return P0(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==poly(o).d
def poly(x):return x if isinstance(x,P0) else P0({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return P0({tuple(e):1})
f,alpha0,c,d0,t=(var(i) for i in range(N));F0=f+1;alpha=alpha0+1;C=c+1;q=F0+alpha+C;G=alpha+(q-F0)*(q-1)
assert all(x>=0 for x in (q*q-2-G).d.values())
# Exception: d=d0+1, F=1+e, b=1+td+e, alpha=1+t(d+1).
e=f;d=d0+1;b=1+t*d+e;q=1+b;alpha=1+t*(d+1);F0=1+e;G=alpha+(q-F0)*b
assert G==q+t*(1+q*d)
assert q*q-2-G==t*(d-1)+t*d*e+3*e+e*e
# Rank upper cap is strictly below q^4 for q>=2.
q=var(0)+2;cap=(q*q-2)*(q*q-1)+(q-1)*(1+2*q)+1
assert q*q*q*q-cap==(q-1)*(q+2)
# The compact high digits end in 0, and all listed symbolic digits are <2^67.
B=2**67;mu=2**51-2;padding=2**65-1;last=2**19-1
digits=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[mu]+[0]*1101+[mu]+[0]*3296+[padding]*13+[last,0]
assert len(digits)==8807 and digits[-1]==0 and all(0<=x<B for x in digits)
high=Path('Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean').read_text()
for token in ['List.replicate 1012 0','List.replicate 3296 0','List.replicate 13 padding ++ [lastPadding,0]','def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1']:
 assert token in high,token
low=Path('Lean/DiophantineConsistency/Compact44/CompactListMask.lean').read_text();assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in low
compact=Path('Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in compact
assert 'theorem port_bounds' in compact and 'theorem K_pos' in compact
# GCD control checks the proposed general argument but is not its proof.
for q0 in range(2,80):
 for s in range(4):
  H=3+4*q0**3*s
  g=gcd(H,q0**5)
  assert g in (1,3) and q0%g==0
print(json.dumps({'both_rank_branch_polynomial_identities':True,'rank_cap_slack_identity':True,'actual_fixed_tuple_and_port_recipes_checked':True,'all_four_factor_mod4_receipt_reproduced':True,'standard_full_zero_implies_k_positive':True,'gcd_argument_scope':'standard integers; q-power and model provider claims remain unelaborated','author_receipt_reproduced':True,'lean_executed':False},sort_keys=True,indent=2))
