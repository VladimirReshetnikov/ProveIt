#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-negative-node76-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'4c3ef328f21c6a3082614547b44d83d4a81dcca9983af60b3ac7b589f8403c97','provider_survey.py':'ce2c6e9afe0d0e4c704265ce7bed62efa78203a3c1d5b1408a60412d9c8dba40','source-manifest.json':'ce43eedb50a05a0b70d780c52bb22abc88dcec9ae2869c01f61615e539f43548'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1;n='Sign33NegativeNode76';q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert sha(q)==rows[0]['source_sha256']=='b3aabf0b9b2510dbbb4a18e8747f48700db68b60876252e2cf4c0974360d6637' and rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.'+x for x in ['Sign33StaticNode76','Sign33ReferenceNode76','Norm38ForwardGatesAssembly','Norm38ForwardPrefix']]
for x in ['ι negative = d.y*d.y-d.V*d.V','ι negative + pairValue ι','witnessCoordinates ports u) 76) = 0','forward_gatesHold ι ports u','Sign33StaticNode76.node76 ports w hg','Norm38Forward.forward_prefix','Sign33ReferenceNode76.reference76','ht.trans hc','rw [he, hn]']:assert x in s
survey=(p/'provider_survey.py').read_text();assert 'b6ea4c9b344d3d941803c224ff945d45f5783894e38eba37ab81bf3e68b61536' in survey and 'Sign33StaticNode76' in survey and 'Sign33ReferenceNode76' in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'conditional negative representative cancels node76; no Lean replay'},indent=2,sort_keys=True))
