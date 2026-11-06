#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates09-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'eed77ec4884edfc8f9e6d42e3c9cfec3450935633f60b8fc924c8b44b254171a','provider_survey.py':'650c57659df24a27816efea81755773efa583233ab6fd64b7771d24301c5d8d5','source-manifest.json':'25882e98c5e90b845413519f84cbe5a8785a01b591a2dbf9b30bbd128ed6b4b3','src/DiophantineConsistency/Sign33RingGates09.lean':'a86d7a81fec2a3334317e0aba3db6dab2cf727fc83c9bbbd4adab76dc32e28c9'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingGates09.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='a86d7a81fec2a3334317e0aba3db6dab2cf727fc83c9bbbd4adab76dc32e28c9';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33Lift38','DiophantineConsistency.NormAssignment38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['gate66','gate67','gate68','gate69','gate70','gate71'];assert len(re.findall(r'^#print axioms ',s,re.M))==6
g=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for line in ['⟨66, 64, 65, GateOp.sub⟩','⟨67, 4, 4, GateOp.mul⟩','⟨68, 31, 6, GateOp.mul⟩','⟨69, 68, 54, GateOp.sub⟩','⟨70, 67, 69, GateOp.mul⟩','⟨71, 70, 31, GateOp.sub⟩','let a66 : SignedPair S := pairCompute GateOp.sub a64 a65','let a67 : SignedPair S := ⟨w 29, 0⟩','let a68 : SignedPair S := pairCompute GateOp.mul a31 a6','let a69 : SignedPair S := ⟨w 30, w 31⟩','let a70 : SignedPair S := pairCompute GateOp.mul a67 a69','let a71 : SignedPair S := ⟨w 32, w 33⟩']:assert line in g
assert all('have h := hc.'+x in s for x in ['batch05.2.1','batch05.2.2','batch06.1'])
b5=(d/'research/nine-sharing-sign33-residual-batch05-check/src/DiophantineConsistency/Sign33ResidualBatch05.lean').read_text();b6=(d/'research/nine-sharing-sign33-residual-batch06-check/src/DiophantineConsistency/Sign33ResidualBatch06.lean').read_text()
assert 'ι (v 28)-(ι (v 5)+1)*(ι (v 5)+1)' in b5 and 'ι (v 29)-(((ι (v 20)+(ι (v 11)+1))*(ι (v 7)+1)+ι (v 26))-(ι (v 26)*ι (v 15)+(ι (ports 2)+q ports v*ι (ports 3))*(ι (v 1)+1)))' in b5 and 'ι (v 30)-(ι (v 28)*ι (v 29)-(ι (v 20)+(ι (v 11)+1)))' in b6
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'six uncompiled ring-value graph equations; no Lean replay'},sort_keys=True,indent=2))
