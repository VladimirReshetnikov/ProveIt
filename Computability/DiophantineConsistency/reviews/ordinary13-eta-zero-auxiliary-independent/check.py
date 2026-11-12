#!/usr/bin/env python3
"""Conditional eta-zero auxiliary inequalities and source scope; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
pin('research/ordinary13-eta-zero-index-route-audit/result.json','f7c322965c4f786b72e6014930478a16573c11e1d5843caae779ae9d809145d6')
g=json.loads(pin('research/ordinary13-natural-forced-w86/candidate.json','75d3110827afc1ef14a5ed2367229e81c645d3394beba2c04d255f53ffeefe50'))
geo=pin('research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean','88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77')
bounds=pin('research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean','f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504')
aux=pin('research/ordinary14-aux-root-model-draft/AuxRootBridge.lean','796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7')
gap=pin('research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean','6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68')
ring=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
assert '(heta : 0<eta)' in geo and 'lt_add_of_pos_left _ heta' in geo
for x in ['theorem first_ordinate_large','(hk : 2<k)','theorem strong_f_square_large','theorem strong_Q_gt_one','theorem signed_square_gt_one']:
 assert x in bounds,x
for x in ['theorem no_main_square','theorem two_ordinate_impossible','have hetaEq : eta=1','have hcEq : c=2*Y+1']:
 assert x in gap,x
for x in ['theorem square_gt_of_aux','theorem above_of_positive','theorem positive_aux_coordinate_iff']:
 assert x in aux,x
assert 'theorem nonneg_iff' in ring and 'theorem one_le_of_pos' in ring
rows={r[0]:r for r in g['source']}
for row in [['eta','+','n_eta',1],['kbase','+','eta','n_zeta'],['k','+','kbase',1],['kY','*','Y','k'],['c','+','eta','kY'],['g72','-','g71','Q'],['V','-','g76','c'],['Fa','-','y2','g82'],['out','-','P0123',1]]:assert rows[row[0]]==row
geomcases=0
for X in range(1,9):
 for Y in range(1,9):
  for extra in range(4):
   k=8*X*Y*Y+4+extra;c=Y*k;A=X*Y+Y+2;delta=A*A-1
   assert 0<A<c and 1<c and 0<delta<c**3
   for i in range(1,5):
    I2=(i*c*c)**2
    assert c**4<=I2 and delta*c<c**4
    for f in range(0,10):
     if f*f<=c+1:assert delta*(f*f-1)<I2
   geomcases+=1
# Eta=0, k=2: c=2Y still lies in the generic consecutive-square gap.
for X in range(1,10):
 for Y in range(1,10):
  c=2*Y;A=X*Y+Y+2;delta=A*A-1;N=1+delta*c*c
  assert 1<c<2*A and (A*c-1)**2<N<(A*c)**2
for c in range(2,30):
 for f in range(2,15):
  if f*f<=c+1:continue
  for t in range(-6,7):
   z=f*f*t-c
   assert z*z>1
# One concrete signed auxiliary control; the general argument is ordered-ring algebra.
Q,z,y=2,-29,41
assert (Q-1)*(y*y-z*z)==z*z-1 and y>abs(z) and y-z>0
print(json.dumps({'scope':'conditional eta-zero auxiliary inequalities and source inventory; no graph zero map or Lean','geometry_controls':geomcases,'generic_k2_square_gap_control':True,'signed_ordinate_and_positive_offset_control':True,'existing_bundle_requires_positive_eta':True,'graph_remains_eta_shifted':True,'lean_elaborated':False},sort_keys=True,indent=2))
