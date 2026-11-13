#!/usr/bin/env python3
"""Independent eta-natural geometry delta and offset interfaces; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
o=pin('research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean','88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77')
g=pin('research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src','5ccefb9efd90dad307ffcf55d67597b32a620d02e0a8b09eb88e642474a12782')
s=pin('research/ordinary13-eta-natural-auxiliary-draft/AuxOffsetFacts.lean.src','c00aae1d141ba5f065de39c304c717c2db8b25a581c19c4d36443a6b273fca31')
pin('research/ordinary13-eta-natural-auxiliary-draft/geometry-result.json','4cc1288e3ed996dbea1cf72abb5db6ccb825b2be7cb8ed8a9c25dbefe0011f24')
pin('research/ordinary13-eta-natural-auxiliary-draft/facts-result.json','ca279efc40d28db9c2e854b9b9f2b56072239a216b12f38794770b6d1fd4e358')
pin('reviews/ordinary13-eta-zero-auxiliary-independent/result.json','dcf98bbfed9e3d01c6968eb9e8c0cd2595be8438f22d97904a3a12bfbc2da4e3')
def body(t):return t.split('theorem geometry_of_large_k',1)[1].split('\nend ',1)[0]
expected=body(o).replace(' (heta : 0<eta)','').replace('_<eta+Y*k := lt_add_of_pos_left _ heta','_≤eta+Y*k := le_add_of_nonneg_left (Arithmetic.zero_le eta)')
assert expected==body(g) and 'heta' not in body(g)
assert 'import AuxRootBounds\nimport AuxRootBridge' in s
for x in ['theorem aux_strict_bounds','(hc : 1<c) (hi : 1≤i) (hDelta : 0<Delta)','(hDeltaSmall : Delta<c*c*c)','strong_f_square_large','strong_Q_gt_one','signed_square_gt_one','theorem positive_offset_of_direct','(hQ : 1<Q) (hz : 1<z*z)','(haux : directAux z Q (ι y)=0)','square_gt_of_aux','above_of_positive','nonneg_iff']:
 assert x in s,x
assert '(hy : 0<y)' not in s and '(heta : 0<eta)' not in g
# Geometry controls at eta zero and other natural eta.
for X in range(9):
 for Y in range(1,9):
  for eta in range(4):
   k=8*X*Y*Y+4;A=X*Y+Y+2;c=eta+Y*k;delta=A*A-1
   assert A<c and 1<c and 0<delta<c**3
for z,y,Q in [(-29,41,2),(29,41,2)]:
 assert (Q-1)*(y*y-z*z)==z*z-1 and y*y>z*z>1 and y-z>0
print(json.dumps({'scope':'exact geometry source delta, offset fact premises and finite controls; no Lean','only_eta_hypothesis_removed_from_geometry':True,'positive_offset_no_y_positive_premise':True,'large_k_and_signed_facts_remain_explicit':True,'research_imports_not_built_providers':True,'lean_elaborated':False},sort_keys=True,indent=2))
