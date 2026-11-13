from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-independent-k-norm-boundary-audit')
for name,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(name).read_bytes()).hexdigest()==h,name
# Exact univariate integer polynomials in q; no fixed giant constant expanded.
class P:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,x):
  x=pol(x);d=self.d.copy()
  for k,v in x.d.items():d[k]=d.get(k,0)+v
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.d.items()})
 def __sub__(self,x):return self+-pol(x)
 def __rsub__(self,x):return pol(x)+-self
 def __mul__(self,x):
  x=pol(x);d={}
  for k,v in self.d.items():
   for j,w in x.d.items():d[k+j]=d.get(k+j,0)+v*w
  return P(d)
 __rmul__=__mul__
 def __eq__(self,x):return self.d==pol(x).d
def pol(x):return x if isinstance(x,P) else P({0:x})
q=P({1:1});Y=q*q*q;X=q;m=X*Y*Y;k=2;eta=2*q*q*q*q+4;a=X*Y+Y;c=eta+Y*k;tau=2*m+1;Delta=(3+4*a)+a*a;g=2*(a+2)*(a+2)-1
assert c==2*(a+2)
assert tau*tau==1+m*(m+1)*k*k
assert g*g==1+Delta*c*c
assert eta-2==2*q*q*q*q+2
source=Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text();graph=json.loads(source)
assert graph['witnesses'][6:11]==['n_w','n_s','n_r','n_eta','n_k']
r={x[0]:x[1:] for x in graph['source']}
for n,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],'Y':['*','q3','s'],'kY':['*','Y','n_k'],'c':['+','n_eta','kY'],'a':['+','E','Y'],'Delta':['+','H','g17']}.items():assert r[n]==row,(n,r[n],row)
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
print(json.dumps({'symbolic_partial_norm_counterexample':True,'q_shape':'q=beta+1 with J=1; valid for compact beta','selected_coordinates':'n_w=1,n_s=0,n_k=2,n_eta=2*q^4+4','first_and_main_natural_norm_identities':True,'k_less_than_eta_for_q_at_least_1':True,'full_graph_zero_claim':False,'graph_root_rank_strong_aux_or_early_index_claim':False,'lean_executed':False},sort_keys=True,indent=2))
