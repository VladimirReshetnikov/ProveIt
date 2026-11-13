#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates08-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'f8ea808a1db66367d0e237ba2d8dd487c53eefa4295205bc92fd6469b1296c8e','provider_survey.py':'a26186348fa429c00773b89d9dcaa9e1b9ecedaf84f890fcc6a94cb76e33e2a2','source-manifest.json':'7c9dbd7d0d206de9e395237a8a36d3c85ae4ac2625b5fe8d573f90befa9e6b88','src/DiophantineConsistency/Sign33RingGates08.lean':'ff6e1ca1ce6859441eb5de3d147292c6a88905dc8d50eba7e7ce39dd2856bcce'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates08.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='ff6e1ca1ce6859441eb5de3d147292c6a88905dc8d50eba7e7ce39dd2856bcce';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate60','gate61','gate62','gate63','gate64','gate65'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨60, 30, 59, GateOp.mul⟩','⟨61, 58, 60, GateOp.sub⟩','⟨62, 15, 8, GateOp.add⟩','⟨63, 62, 46, GateOp.mul⟩','⟨64, 63, 45, GateOp.add⟩','⟨65, 3, 21, GateOp.mul⟩','let a60 : SignedPair S := pairCompute GateOp.mul a30 a59','let a61 : SignedPair S := pairCompute GateOp.sub a58 a60','let a62 : SignedPair S := pairCompute GateOp.add a15 a8','let a63 : SignedPair S := pairCompute GateOp.mul a62 a46','let a64 : SignedPair S := pairCompute GateOp.add a63 a45','let a65 : SignedPair S := pairCompute GateOp.mul a3 a21']:assert line in g
assert 'AllCuts' not in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
