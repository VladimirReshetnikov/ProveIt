#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-q-retry02';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'145e700b26797c4e67c0ef6e062fbfdf1ba9897b0479ad32126db140c104cba8','provider_survey.py':'e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25','source-manifest.json':'f7df36612bee882a53ebc302265ff1ebecbba943796f4ad41e0f215ced9327d6'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33ForwardNormQ38','ec9ebdcf4a47359057753b26273097ac8268e67bbd99c2c05a6ba31f7569f620',['Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix']),('Sign33ForwardNormQRetry','fa32302f00b528286f619e523675c4dae1c39b49e65eb3edbd5c7da1fa605f69',['Sign33ForwardNormQ38','SharingForward33'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports]
a=(p/'src/DiophantineConsistency/Sign33ForwardNormQ38.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ForwardNormQRetry.lean').read_text()
for x in ['d.Q = 1','forward_gatesHold ι ports u','static_terminals_agree','forward_prefix','reference_terminal_fields_combined','ht.2.1.trans (hc.2.1.trans hq)']:assert x in a
for x in ['d.Q = 1','ι (v 23)*ι (v 23)-ι (v 25) = 1','Sign33ForwardNormQ38.q_terminal ports u hq','rw [hs] at ht','map_add, map_mul','SharingForward38.witnessCoordinates ports u 22','SharingForward38.witnessCoordinates ports u 24']:assert x in b
nodes=(d/'research/nine-sharing-norm38-model-bridge-draft/NormAssignment38.lean').read_text()
for x in ['let a40 : SignedPair S := ⟨w 22, 0⟩','let a42 : SignedPair S := ⟨w 24, 0⟩','let a43 : SignedPair S := pairCompute GateOp.mul a40 a40','let a44 : SignedPair S := pairCompute GateOp.sub a43 a42']:assert x in nodes
f=(d/'research/nine-sharing-sign33-forward-constructor-check/src/DiophantineConsistency/SharingForward33.lean').read_text();part=f.split('def witnessCoordinates',1)[1].split('theorem witness_inputs',1)[0];vec=[x.strip() for x in re.search(r'!\[(.*?)\]',part,re.S).group(1).split(',')];assert vec[22]=='w 22' and vec[24]=='w 24'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional Q bridge and coordinate transfer; no Lean replay'},indent=2,sort_keys=True))
