#!/usr/bin/env python3
"""Pinned source interface and finite exact square-gap controls, no Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean':'6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68',
'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean':'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504',
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5'}
def pin(p,h):
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={p:pin(p,h) for p,h in pins.items()}
assert 'theorem no_main_square (A c Delta d : V) (hA : 0<A) (hc : 1<c)' in s['research/ordinary14-model-main-square-gap-draft/MainSquareGap.lean']
assert 'theorem first_ordinate_large (m tau k : V) (hm : 0<m) (hk : 2<k)' in s['research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean']
assert 'theorem two_le_ordinate (q x k : V) (hk : 0<k)' in s['Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean']
b=(here/'EtaNaturalNormLargeK.lean.src').read_bytes();v=b.decode()
assert '(hX : 0<X) (hY : 0<Y) (hzeta : 0<zeta)' in v and '(heta :' not in v
for term in ('theorem two_ordinate_impossible','theorem large_first_ordinate','no_main_square','two_le_ordinate','first_ordinate_large'):assert term in v
assert 'sorry' not in v and '\naxiom ' not in v
controls=0
for X in range(1,20):
 for Y in range(1,25):
  for eta,zeta in ((0,2),(1,1)):
   A=X*Y+Y+2;c=eta+Y*(eta+zeta);D=A*A-1
   assert 1<c<2*A
   assert (A*c-1)**2 < 1+D*c*c < (A*c)**2
   controls+=1
for m in range(1,1000):
 assert m*m < 1+m*(m+1) < (m+1)*(m+1)
print(json.dumps({'source_sha256':pins,'draft_sha256':hashlib.sha256(b).hexdigest(),'k2_gap_controls':controls,'k1_gap_controls':999,'lean_elaborated':False,'scope':'lexical source interfaces and bounded integer controls; not an IΣ₁ proof or graph extraction'},sort_keys=True,indent=2))
