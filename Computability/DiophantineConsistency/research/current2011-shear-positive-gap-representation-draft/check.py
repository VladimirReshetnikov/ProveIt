from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current2011-shear-positive-gap-representation-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'PositiveGapRepresentation.lean.src').read_text();r=Path('Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text()
for t in ['theorem positive_as_successor (D : DiffRing V) (hD : 0 < D)','∃ n : V, ι (n+1) = D','nonneg_iff.mp (le_of_lt hD)','tsub_add_cancel_of_le ha1','theorem positive_gap_as_successor','ι (n+1) = yParent-signedV']:
 assert t in s,t
assert 'theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in r
count=0
for y in range(-10,21):
 for z in range(-10,21):
  if z<y:
   n=y-z-1
   assert n>=0 and n+1==y-z
   count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'nonnegative_representation_interface_checked':True,'finite_gap_controls':count,'lean_executed':False,'model_theorem_or_provider_authenticated':False},sort_keys=True,indent=2))
