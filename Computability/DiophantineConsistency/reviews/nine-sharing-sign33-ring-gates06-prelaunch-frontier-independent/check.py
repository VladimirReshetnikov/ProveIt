#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates06-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'54227bf7286eeb6b6afd9e8b4d0bbc4c5e0fbbe6bab4cb1cb8c7cec638cf20fd','provider_survey.py':'5c822b4f812a71dd10f77171b7d39087fc158e7c892931ec7b56bf048756ea1b','source-manifest.json':'387a9ae104402016eaa3117936cd4d23f0fc3a9ef418f77ac57106fa4a28f6f3','src/DiophantineConsistency/Sign33RingGates06.lean':'8af4324714e056003d46d4d55d8282aa8e9f0b64c6f5a01edef3b915ff827913'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates06.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='8af4324714e056003d46d4d55d8282aa8e9f0b64c6f5a01edef3b915ff827913';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate48','gate49','gate50','gate51','gate52','gate53'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨48, 47, 2, GateOp.add⟩','⟨49, 23, 18, GateOp.sub⟩','⟨50, 48, 49, GateOp.mul⟩','⟨51, 22, 17, GateOp.mul⟩','⟨52, 16, 51, GateOp.add⟩','⟨53, 52, 0, GateOp.mul⟩','let a48 : SignedPair S := ⟨w 25, w 26⟩','let a49 : SignedPair S := pairCompute GateOp.sub a23 a18','let a50 : SignedPair S := pairCompute GateOp.mul a48 a49','let a51 : SignedPair S := pairCompute GateOp.mul a22 a17','let a52 : SignedPair S := pairCompute GateOp.add a16 a51','let a53 : SignedPair S := pairCompute GateOp.mul a52 a0']:assert line in g
assert 'have h := hc.batch04.1' in s and 'simp only [Sign33ResidualBatch04.t] at h' in s
batch=(d/'research/nine-sharing-sign33-residual-batch04-check/src/DiophantineConsistency/Sign33ResidualBatch04.lean').read_text();assert 'ι (v 26)-((t ports v*(t ports v+1)+(ι (v 3)+1))-t ports v*(ι (v 2)+1))' in batch
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
