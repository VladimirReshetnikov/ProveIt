#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates03-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'8d58acb3bb5b7dbd017c3de4fc9b81b2889d61bd794e3a3dedd97c5350dcfe90','provider_survey.py':'cec2d653a0a229fd8639689ed82fae5c4de404f6fd91b84c76858d432f6cf5b5','source-manifest.json':'5d9516dc3c0a214361600f297fe032b1bd0de0954791d7f71353809169e0c7e5','src/DiophantineConsistency/Sign33RingGates03.lean':'f90cc7222e7e8eab85dec5f5d5e45a5030e39f1e9c316b522a4ce81302755a59'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates03.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='f90cc7222e7e8eab85dec5f5d5e45a5030e39f1e9c316b522a4ce81302755a59';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate30','gate31','gate32','gate33','gate34','gate35'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨30, 27, 29, GateOp.mul⟩','⟨31, 29, 10, GateOp.add⟩','⟨32, 27, 26, GateOp.add⟩','⟨33, 20, 32, GateOp.mul⟩','⟨34, 33, 19, GateOp.add⟩','⟨35, 32, 32, GateOp.mul⟩','let a30 : SignedPair S := ⟨w 20, 0⟩','let a31 : SignedPair S := pairCompute GateOp.add a29 a10','let a32 : SignedPair S := pairCompute GateOp.add a27 a26','let a33 : SignedPair S := pairCompute GateOp.mul a20 a32','let a34 : SignedPair S := pairCompute GateOp.add a33 a19','let a35 : SignedPair S := pairCompute GateOp.mul a32 a32']:assert line in g
assert 'have h := hc.batch02.1' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
