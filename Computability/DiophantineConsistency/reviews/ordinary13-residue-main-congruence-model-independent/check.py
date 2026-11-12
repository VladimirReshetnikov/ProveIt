#!/usr/bin/env python3
"""Independent actual-main pair, arithmetic tuple and exact balance audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src','c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8')
pin('research/ordinary13-residue-main-congruence-model-draft/receipt.json','ac2ce7760b3fcc5448f507b19cb7a0620d0ae113500f624b6893e517dac4e168')
pin('reviews/ordinary13-residue-first-index-model-independent/result.json','4340b4c32ca888c55358b8401a468b44506c5c231bd8a9bedbb3c54e53c4feac')
pin('reviews/ordinary13-residue90-xzero-graph-independent/result.json','ffa967831cfed486dca16c9f3bbf9a3735fcc0e298c13b1cfc124a19b8b0cc6e')
for x in ['![v 0,v 1+1,v 2+1,v 3,v 4+1,v 6,Y p v,v 5+1,v 9+1,v 10+1,v 11,v 12]','rank p v+v 6*Y p v*q p v','theorem main_pair_identity','rank_representation p v hFq','theorem actual_main_magnitude_norm','Residue90SignedNormsDraft.main_pair_norm','theorem arithmetic_congruence_of_balance','linear_combination hbalance','FreeJMainOrientation.FreeJMainCongruence','DirectMainNorm.direct_main_orientation','FreeJMainOrientation.rank_congruence_from_main','theorem early_index_of_actual_graph','ResidueFirstIndexModelDraft.early_index_of_natural_norm','(hR24 : 24≤rank p v)','(hwindow : rank p v+']:
 assert x in s,x
# Free-ring checks for actual shift P-N=Dstar and regrouped balance.
def v(x):return {(x,):1}
def add(a,b,k=1):
 d=a.copy()
 for t,c in b.items():d[t]=d.get(t,0)+k*c
 return {t:c for t,c in d.items() if c}
def mul(a,b):
 d={}
 for x,u in a.items():
  for y,vv in b.items():
   t=tuple(sorted(x+y));d[t]=d.get(t,0)+u*vv
 return {t:c for t,c in d.items() if c}
one={():1};U,X,A,C,H,G,E,q,R,k,s0,main,qp=map(v,['U','X','a','c','H','gamma','E','q','R','k','s','main','q5'])
Eq=mul(E,q);base=mul(U,add(X,mul(A,C)));P=add(base,mul(H,add(add(mul(U,G),add(R,Eq)),one)));N=mul(H,k)
Dstar=add(base,mul(H,add(add(add(mul(U,G),Eq),R),add(one,k,-1))))
assert add(P,N,-1)==Dstar
# Replace U by q⁵*s in P=N+U*main and compare the proposed grouped equation.
Uq=mul(qp,s0);Pq=add(mul(Uq,add(X,mul(A,C))),mul(H,add(add(mul(Uq,G),add(R,Eq)),one)))
source=add(add(Pq,N,-1),mul(Uq,main),-1)
target=add(add(mul(H,add(add(Eq,R),one)),mul(qp,mul(s0,add(add(X,mul(A,C)),mul(H,G))))),add(N,mul(qp,mul(s0,main))),-1)
assert source==target
# On natural models truncated rank representation needs F≤q; outside it q-F differs from signed subtraction.
for q0 in range(1,8):
 for F in range(0,q0+1):assert max(q0-F,0)==q0-F
assert max(2-3,0)!=2-3
print(json.dumps({'scope':'actual signed main pair and abstract balance identities, source interface; no Lean','adjusted_rank_R_plus_XYq':True,'rank_cast_requires_F_le_q':True,'freeJ_tuple_is_arithmetic_only':True,'early_not_exact_index':True,'port_and_graph_assumptions_explicit':True,'lean_elaborated':False},sort_keys=True,indent=2))
