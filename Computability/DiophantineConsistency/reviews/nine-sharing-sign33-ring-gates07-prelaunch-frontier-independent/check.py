#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates07-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'c6fb2ef34dafc81502f5205c9f34eb5d929fc73147e2faf12c6de4e56f61a203','provider_survey.py':'2be1733ca581f2f88a4e322562970367adade53d161fd834ca63122ccb9df895','source-manifest.json':'e2a92dc40f79f4f9a80f02f281cf4756644269a44f70196e2067590854744ec7','src/DiophantineConsistency/Sign33RingGates07.lean':'1906127d0dbfebcf7a4fdf78f7087baa01d90f8e736a7304d903a8816e8af71d'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates07.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='1906127d0dbfebcf7a4fdf78f7087baa01d90f8e736a7304d903a8816e8af71d';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate54','gate55','gate56','gate57','gate58','gate59'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨54, 50, 53, GateOp.add⟩','⟨55, 27, 9, GateOp.mul⟩','⟨56, 55, 28, GateOp.add⟩','⟨57, 56, 54, GateOp.sub⟩','⟨58, 57, 57, GateOp.mul⟩','⟨59, 30, 28, GateOp.add⟩','let a54 : SignedPair S := pairCompute GateOp.add a50 a53','let a55 : SignedPair S := pairCompute GateOp.mul a27 a9','let a56 : SignedPair S := pairCompute GateOp.add a55 a28','let a57 : SignedPair S := ⟨w 27, w 28⟩','let a58 : SignedPair S := pairCompute GateOp.mul a57 a57','let a59 : SignedPair S := pairCompute GateOp.add a30 a28']:assert line in g
assert 'have h := hc.batch04.2.1' in s and 'simp only [Sign33ResidualBatch04.q, Sign33ResidualBatch04.t] at h' in s
batch=(d/'research/nine-sharing-sign33-residual-batch04-check/src/DiophantineConsistency/Sign33ResidualBatch04.lean').read_text();assert 'ι (v 27)-(((ι (v 19)*(ι (v 10)+1)+((ι (v 11)+1)+(ι (v 12)+1)))+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1)))' in batch
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
