#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates01-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'dfade7a43b03779c5a44212575eefab979092d441a1fa4ec8cd356464c83d2b5','provider_survey.py':'64995569ac89081e5f0a6dd39f420cdeffcef4c95225e634d237cf9fb0061e5b','source-manifest.json':'4fd691d84fa9675e56224cddae6f9a987a5f3465d26d93eb6cfb2603d8698932','src/DiophantineConsistency/Sign33RingGates01.lean':'72a0e785ebb71b7caaabdc9609afef9a9b7fd87b2e92f4b12e20b4a324009ea9'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates01.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='72a0e785ebb71b7caaabdc9609afef9a9b7fd87b2e92f4b12e20b4a324009ea9';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate24','gate25','gate26'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨24, 23, 22, GateOp.mul⟩','⟨25, 8, 22, GateOp.mul⟩','⟨26, 7, 24, GateOp.mul⟩','let a24 : SignedPair S := ⟨w 15, 0⟩','let a25 : SignedPair S := ⟨w 16, 0⟩','let a26 : SignedPair S := ⟨w 17, 0⟩']:assert line in g
assert all('have h := hc.'+x in s for x in ['batch00.2.1','batch00.2.2','batch01.1'])
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
