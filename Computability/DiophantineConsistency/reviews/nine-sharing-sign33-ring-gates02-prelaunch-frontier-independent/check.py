#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates02-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'d4ce92bb1687dfb91c28644ea1f69b56c07b2f9afc67d4f977729dedddd6ce66','provider_survey.py':'e6d7a7b8c639a4883c5b1dc3c60b3c4f2ad9ff9b20cc6783afb9d92e6ed4c6dd','source-manifest.json':'36874c1a24fb96df13438677fbbfdf9778c85283d7aa217caa7e96e718a67008','src/DiophantineConsistency/Sign33RingGates02.lean':'c417b34168c5829933e9350f3a24f59d62c22310c2d8a4ef421d7d9e71b67e65'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates02.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='c417b34168c5829933e9350f3a24f59d62c22310c2d8a4ef421d7d9e71b67e65';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate27','gate28','gate29'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨27, 25, 26, GateOp.mul⟩','⟨28, 10, 11, GateOp.add⟩','⟨29, 28, 26, GateOp.mul⟩','let a27 : SignedPair S := ⟨w 18, 0⟩','let a28 : SignedPair S := pairCompute GateOp.add a10 a11','let a29 : SignedPair S := ⟨w 19, 0⟩']:assert line in g
assert all('have h := hc.'+x in s for x in ['batch01.2.1','batch01.2.2'])
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
