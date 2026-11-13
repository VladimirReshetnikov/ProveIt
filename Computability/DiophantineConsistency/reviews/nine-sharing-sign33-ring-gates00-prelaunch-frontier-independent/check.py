#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates00-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'2ad5d1e4b6e6583163a83907ac5e0ce2963b1be8e9e86638ab0cd6c0a7701ed7','provider_survey.py':'567f9a361d5fb3f4b6c52b2a7430046917fd5e1bdd3f38cf81e68523a545a852','source-manifest.json':'ab5e551f3f0271e9b30e5e388d6bca60ba7eb570e59df228cc275fe72231dd83','src/DiophantineConsistency/Sign33RingGates00.lean':'25a4150e676deee3d011394e07efa399649bf25a2eca94d1266205f09d5029cf'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates00.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='25a4150e676deee3d011394e07efa399649bf25a2eca94d1266205f09d5029cf';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate21','gate22','gate23'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨21, 14, 0, GateOp.mul⟩','⟨22, 21, 18, GateOp.add⟩','⟨23, 22, 22, GateOp.mul⟩','let a23 : SignedPair S := ⟨w 14, 0⟩']:assert line in g
assert '(hc : Sign33ResidualAssembly.AllCuts ports v)' in s and 'have h := hc.batch00.1' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'three uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
