#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group03-positive-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'a15dd855a73a1575b0fd9b156c4e82e2ac84522c772378378f9b3832917b1f8f','provider_survey.py':'6aec5c9a34b9c1c40e55ec6565d6b18896dc1a0f5911fa5fb8518158b41f2122','source-manifest.json':'6b2f8df440f13e55798d0ad0fa5a96846038b04fb63348f563ee6fe1286d1190','src/DiophantineConsistency/Sign33ForwardGroup03Positive.lean':'e02d67ef01e58d92d65ab643991d00e7dcc63079308279b81d6ff6330dd4230e'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardGroup03Positive.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='e02d67ef01e58d92d65ab643991d00e7dcc63079308279b81d6ff6330dd4230e';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly'];assert re.findall(r'^theorem (\w+)',s,re.M)==['constructor_cuts']
a=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('def condition',1)[1].split('theorem constructor_cuts',1)[0].split(':=',1)[1];batch=a.split('  batch03 :',1)[1].split('  batch04 :',1)[0].rsplit('∧',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
assert 'Fin.cons (1 : V)' in s and '(gap tau inner value negative : V)' in s
f=(d/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/ForwardWitness38.lean').read_text();assert all(f'let w{j} : S :=' in f for j in (24,25))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'forward first two equations of fourth AllCuts batch source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
