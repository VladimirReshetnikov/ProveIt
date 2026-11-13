from pathlib import Path
from hashlib import sha256
import sys,json,re,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-positive-composition-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary13-independent-k-rank-representation-draft','ordinary13-independent-k-zero-graph-fact-binding-draft','ordinary13-independent-k-fixed-compact-port-client-draft'):
 p=Path('research')/name
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(D/'IndependentKPositiveComposition.lean.src').read_text();n=lambda x:re.sub(r'\s+',' ',x)
for x in ['theorem rankRing_eq_expr','theorem rank_represented','theorem k_positive',
 'have hJ := child_J_positive v hz','have hf := first_norm v hz hk',
 'IndependentKRankRepresentationDraft.first_norm_F_lt_q',
 'IndependentKRankRepresentationDraft.rank_representation natPorts v hFq\'',
 'zero_k_impossible_of_rank_representation v','(Residue90GraphNormsDraft.rank natPorts v) hz hk (rank_represented v hz hk)']:
 assert x in s,x
assert n('(q v) (natPorts 0:V) (v 0) (v 1+1) (v 2+1) (X v+(natPorts 1:V)) (v 8) rfl hb hJ hF hf') in n(s)
assert n('(hz : InternalZero (graph intPorts).output v) : 0<v 10') in n(s)
# Independent free-ring expansion of graph-client versus rankExpr valuation;
# q=beta*J+1 vs q=1+J*beta is accounted for by actual commutative arithmetic.
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
def var(i):
 e=[0]*N;e[i]=1;return P({tuple(e):1})
J,F,alpha,beta,MC,MF=(var(i) for i in range(N));q=beta*J+1;q0=1+J*beta
r1=(alpha+(q-F)*(beta*J))*(q*q-1)+J*(MC+q*MF)
r2=(alpha+(q0-F)*(J*beta))*(q0*q0-1)+J*(MC+MF*q0)
assert r1==r2
# Both first norm branch and extracted F≤q controls, including arbitrary alpha and d=0.
pos=nonpos=0
for beta0 in range(1,8):
 for J0 in range(1,5):
  q0=beta0*J0+1;b=q0-1
  for F0 in range(1,q0+3):
   for alpha0 in range(q0+3):
    C=q0-F0-alpha0
    for d in range(4):
     Bt=C*d-F0
     for r in range(3):
      if (b*r-Bt)**2==b*b:
       assert F0<q0
       if C>0:pos+=1
       else:nonpos+=1
print(json.dumps({'three_source_receipts_reproduced':True,'composition_argument_order_and_only_zero_premise_checked':True,'independent_signed_rank_polynomial_identity':True,'positive_C_controls':pos,'nonpositive_C_controls':nonpos,'rank_helper_orientation_requires_independent_review':True,'lean_executed':False,'provider_or_axiom_validation':False},sort_keys=True,indent=2))
