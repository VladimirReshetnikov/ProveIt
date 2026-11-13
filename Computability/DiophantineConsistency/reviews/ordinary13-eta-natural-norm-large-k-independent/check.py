#!/usr/bin/env python3
"""Independent eta-natural k=1/2 gap and source premises audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src','aac1707680c5894a8dde85b63fba8b4c1417f8e7296022a2c686ac3928caaa06')
pin('research/ordinary13-eta-natural-norm-large-k-draft/result.json','c18a68a9591abe10ed530aa71c17a85b84213d3261472dcf7beecaebc9a197f2')
pin('reviews/ordinary13-eta-zero-auxiliary-independent/result.json','dcf98bbfed9e3d01c6968eb9e8c0cd2595be8438f22d97904a3a12bfbc2da4e3')
gap=pin('research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean','6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68')
first=pin('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
bounds=pin('research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean','f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504')
assert 'import MainSquareGap\nimport AuxRootBounds' in s
for x in ['theorem two_ordinate_impossible','(hX : 0<X) (hY : 0<Y) (hzeta : 0<zeta)','have hetale : eta≤1','have hcEq : c=eta+2*Y','apply no_main_square A c Delta d hA hc hcA','theorem large_first_ordinate','have hm : 0<m','tsub_add_cancel_of_le (pos_iff_one_le.mp hm)','two_le_ordinate (m-1) tau k hk hn\'','first_ordinate_large m tau k hm hkgt hn']:
 assert x in s,x
assert '(heta : 0<eta)' not in s
assert 'theorem no_main_square (A c Delta d : V)' in gap and 'theorem two_le_ordinate' in first and 'theorem first_ordinate_large' in bounds
cases=0
for X in range(1,20):
 for Y in range(1,20):
  for eta,zeta in [(0,2),(1,1)]:
   assert eta+zeta==2 and zeta>0 and eta<=1
   A=X*Y+Y+2;c=eta+2*Y;delta=A*A-1;N=1+delta*c*c
   assert 1<c<2*A and (A*c-1)**2<N<(A*c)**2
   cases+=1
for M in range(1,1000):assert M*M<1+M*(M+1)<(M+1)**2
print(json.dumps({'scope':'explicit norm premises, square-gap source interfaces and finite controls; no Lean','eta_zero_and_one_k2_cases_checked':True,'zeta_positivity_required':True,'first_norm_k1_gap_checked':True,'large_k_descent_provider_unelaborated':True,'graph_norms_not_supplied':True,'finite_k2_cases':cases,'lean_elaborated':False},sort_keys=True,indent=2))
