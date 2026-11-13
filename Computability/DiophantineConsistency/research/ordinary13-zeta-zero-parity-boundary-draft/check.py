from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-zero-parity-boundary-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'ZetaZeroParityBoundary.lean.src').read_text()
for t in ['ZetaZeroNormLargeKDraft.large_first_ordinate X Y k tau D g','AuxGeometryEtaNaturalDraft.geometry_of_large_k X Y k k D','let c:=k+Y*k','let c : V := k+Y*k','ZetaZeroIndexParityDraft.zeta_zero_contradiction','ArithmeticPellClassification.solution_index a g c hg','EtaNaturalStrongAuxDraft.index_aux_of_direct']:
 assert t in s,t
checks=0
for X in range(1,35):
 for Y in range(1,35):
  for j in range(3):
   k=8*X*Y*Y+4+j;a=X*Y+Y;delta=3+4*a+a*a;c=k+Y*k
   assert 1<c and 0<delta<c**3 and (a+2)**2==delta+1
   checks+=1
print(json.dumps({'zeta_zero_geometry_controls':checks,'same_n_w_and_root_arguments_explicit':True,'graph_binding_proved':False,'lean_executed':False},sort_keys=True,indent=2))
