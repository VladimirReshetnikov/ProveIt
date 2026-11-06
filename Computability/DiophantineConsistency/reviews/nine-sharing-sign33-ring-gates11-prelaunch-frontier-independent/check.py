#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates11-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'177bb5e96e4f17312b3c103f3b78d892f8d9894fa5c62fc7c7f1fed79fc658d9','provider_survey.py':'71a1e4f86d8adf34dcba4b3d8c6ada617174d5e633c1b4f215e2cc783db1dac5','source-manifest.json':'a191c872aee395b6af011fdbfa1375de18b7942a9a5f45966ff43f916558fa7b','src/DiophantineConsistency/Sign33RingGates11.lean':'89f295708e83fbd98d80b7c0e37cfb00ee8a9ac74313aff2c5f5472e96f6c631'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates11.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='89f295708e83fbd98d80b7c0e37cfb00ee8a9ac74313aff2c5f5472e96f6c631';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate78','gate79','gate80'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨78, 77, 75, GateOp.add⟩','⟨79, 36, 67, GateOp.mul⟩','⟨80, 79, 73, GateOp.sub⟩','let a78 : SignedPair S := pairCompute GateOp.add a77 a75','let a79 : SignedPair S := pairCompute GateOp.mul a36 a67','let a80 : SignedPair S := pairCompute GateOp.sub a79 a73']:assert line in g
assert 'AllCuts' not in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
