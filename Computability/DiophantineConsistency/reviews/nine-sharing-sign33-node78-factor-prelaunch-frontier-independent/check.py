#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-node78-factor-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'be4538f5ec9ea283668ec850822cf219bd65995c56a4e157b4abf4ea6ab629e6','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'0e434d9ce41582a5222c89943fd605439ed99a8d61d7da8f82ea14c153246023'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33Node78Factor';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='4b55772f4ce4f7fb71a38a649183144c3e032150c29f0c4330009581acb74577' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.NormAssignment38']
for x in ['[CommSemiring S] [CommRing R]','(embed : S →+* R)','assignment ports w 78','embed (w 35) * pairValue embed (NormAssignment38.assignment ports w 76)','embed (w 12+1)*embed (w 12+1)']:assert x in s
ref=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for x in ['let a12 : SignedPair S := ⟨w 12 + 1, 0⟩','let a73 : SignedPair S := ⟨w 35, 0⟩','let a75 : SignedPair S := pairCompute GateOp.mul a12 a12','let a76 : SignedPair S := ⟨w 36, w 37⟩','let a77 : SignedPair S := pairCompute GateOp.mul a73 a76','let a78 : SignedPair S := pairCompute GateOp.add a77 a75']:assert x in ref
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'generic embedded node78 factor identity; no Lean replay'},indent=2,sort_keys=True))
