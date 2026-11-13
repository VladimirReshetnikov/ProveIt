from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear72-reverse-generic-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
source=(D/'Shear72ReverseGenericModel.lean.src').read_text()
for t in ['import DiophantineConsistency.ShearNonzero','import DiophantineConsistency.Shear72ReverseMagnitude','(hA : 0 ≤ A) (hI : 2 ≤ I) (hy : 1 ≤ y)','ordinate_ne_zero A I Vr (ι y) (P^2+(QW-1)^2) hA hI hy\' hrest hzero','positive_magnitude (Vr+ι y) hn','auxiliary_of_same_square A Vr (ι yOld) (ι y) hs']:
 assert t in source,t
a=Path('research/current2011-shear-ordinate-nonzero-order-draft/ShearNonzero.lean.src').read_text()
for t in ['theorem ordinate_ne_zero (A I V y rest : R)','(hA : 0 ≤ A) (hI : 2 ≤ I) (hy : 1 ≤ y) (hrest : 0 ≤ rest)','V+y ≠ 0']:
 assert t in a,t
b=Path('research/current2011-shear72-reverse-magnitude-draft/Shear72ReverseMagnitude.lean.src').read_text()
for t in ['theorem positive_magnitude (z : DiffRing V) (hz : z ≠ 0)','theorem auxiliary_of_same_square (A Vr yOld yShift : DiffRing V)']:
 assert t in b,t
count=0
for A in range(10):
 for I in range(2,6):
  for y in range(1,5):
   for P in range(-3,4):
    for QW in range(-3,4):
     V=-y
     assert P*P+(QW-1)**2+(A*y*y)**2+(I*I-A)**2>2
     count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'source_interface_shapes_checked':True,'zero_ordinate_integer_controls':count,'graph_to_facts_proved':False,'lean_executed':False},sort_keys=True,indent=2))
