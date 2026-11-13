#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates04-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'277d1fb3090718d09c06f0e16b39e6455feabbf0707d3e22bd6134d029600ef5','provider_survey.py':'25e5adaf69772ff196b8230cc0754c6523913366f27d47d787ccf06265455f2b','source-manifest.json':'1b87f67b9bd1089a81e16357836569d4e0bbe24eb842fb5547129fade2f4fdd4','src/DiophantineConsistency/Sign33RingGates04.lean':'9bfb26008806fb305d244c8b6482dde299f195b62997c0ae9fb502a6383dca4c'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates04.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='9bfb26008806fb305d244c8b6482dde299f195b62997c0ae9fb502a6383dca4c';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate36','gate37','gate38','gate39','gate40','gate41'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨36, 35, 34, GateOp.add⟩','⟨37, 32, 31, GateOp.mul⟩','⟨38, 25, 37, GateOp.add⟩','⟨39, 13, 34, GateOp.mul⟩','⟨40, 38, 39, GateOp.add⟩','⟨41, 31, 31, GateOp.mul⟩','let a36 : SignedPair S := ⟨w 21, 0⟩','let a37 : SignedPair S := pairCompute GateOp.mul a32 a31','let a38 : SignedPair S := pairCompute GateOp.add a25 a37','let a39 : SignedPair S := pairCompute GateOp.mul a13 a34','let a40 : SignedPair S := ⟨w 22, 0⟩','let a41 : SignedPair S := ⟨w 23, 0⟩']:assert line in g
assert all('have h := hc.'+x in s for x in ['batch02.2.1','batch02.2.2','batch03.1'])
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
