#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates05-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'cc2311cd559d4de3477aa71d66b7c9897a9cf7ebd36e41521ab9cb45514da515','provider_survey.py':'05f94554db4091620c7a94c07108eb322a0c10f62ed1c3adeb511dd254802d55','source-manifest.json':'372ec0242a5555c90ad2f51dcaaf77bd6a162440b4afa999528e200e98783b83','src/DiophantineConsistency/Sign33RingGates05.lean':'27c9b233f5ae2825bb4929a662b3383378943d996e23bcd9566195b5fd27e39a'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates05.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='27c9b233f5ae2825bb4929a662b3383378943d996e23bcd9566195b5fd27e39a';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate42','gate43','gate44','gate45','gate46','gate47'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨42, 36, 41, GateOp.mul⟩','⟨43, 40, 40, GateOp.mul⟩','⟨44, 43, 42, GateOp.sub⟩','⟨45, 22, 1, GateOp.sub⟩','⟨46, 45, 2, GateOp.sub⟩','⟨47, 21, 45, GateOp.mul⟩','let a42 : SignedPair S := ⟨w 24, 0⟩','let a43 : SignedPair S := pairCompute GateOp.mul a40 a40','let a44 : SignedPair S := pairCompute GateOp.sub a43 a42','let a45 : SignedPair S := pairCompute GateOp.sub a22 a1','let a46 : SignedPair S := pairCompute GateOp.sub a45 a2','let a47 : SignedPair S := pairCompute GateOp.mul a21 a45']:assert line in g
assert 'have h := hc.batch03.2.1' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
