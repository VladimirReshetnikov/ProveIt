#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates10-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'f21c3a06365d15ebf663fd038293e62377c1a78d43e264df6523bbb22de47619','provider_survey.py':'624b787774c6de67010e13639bee87b1c4aa4d9b0827621d463b486e4a80b220','source-manifest.json':'abf7f1c4fcd77b593f50b7f9e830de8b4cb91ca1fef05c1a2673146363f86ae8','src/DiophantineConsistency/Sign33RingGates10.lean':'654ac31a6b1567e70ba076049caae3e7bea28e5a427fcbb492b696dfd10fdd20'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates10.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='654ac31a6b1567e70ba076049caae3e7bea28e5a427fcbb492b696dfd10fdd20';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate72','gate73','gate74','gate75','gate76','gate77'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨72, 5, 42, GateOp.mul⟩','⟨73, 72, 72, GateOp.mul⟩','⟨74, 71, 71, GateOp.mul⟩','⟨75, 12, 12, GateOp.mul⟩','⟨76, 74, 75, GateOp.sub⟩','⟨77, 73, 76, GateOp.mul⟩','let a72 : SignedPair S := ⟨w 34, 0⟩','let a73 : SignedPair S := ⟨w 35, 0⟩','let a74 : SignedPair S := pairCompute GateOp.mul a71 a71','let a75 : SignedPair S := pairCompute GateOp.mul a12 a12','let a76 : SignedPair S := ⟨w 36, w 37⟩','let a77 : SignedPair S := pairCompute GateOp.mul a73 a76']:assert line in g
assert all('have h := hc.'+x in s for x in ['batch06.2.1','batch06.2.2','batch07.1'])
b6=(d/'research/nine-sharing-sign33-residual-batch06-check/src/DiophantineConsistency/Sign33ResidualBatch06.lean').read_text();b7=(d/'research/nine-sharing-sign33-residual-batch07-check/src/DiophantineConsistency/Sign33ResidualBatch07.lean').read_text();lift=(d/'research/nine-sharing-sign33-lift38-check/src/DiophantineConsistency/Sign33Lift38.lean').read_text()
assert 'ι (v 31)-((ι (v 6)+1)*ι (v 25))' in b6 and 'ι (v 32)-(ι (v 31)*ι (v 31))' in b6 and 'ι (v 33)-((ι (v 13)+1)*(ι (v 13)+1)-ι (v 30)*ι (v 30))' in b7 and 'lift v 36 = 0 ∧ lift v 37 = v 33' in lift
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
