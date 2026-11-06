#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group01-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'fe39deed805439b6a70f97c366c681644ac1802507ebb864eb8e26188e09217c','provider_survey.py':'48f70e21e45814a6948498b3ddc78e3e013eed25105136ec2c36ddbdaae5b576','source-manifest.json':'729f150c63a64d8c862de43924482699bdaeb0f725f5322bce30e1337bb3060f','src/DiophantineConsistency/Sign33ForwardGroup01.lean':'baddb6b73d4f98ef664c2a5bd91937ef659740a5ddd8e6056c32f003651a600e'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardGroup01.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='baddb6b73d4f98ef664c2a5bd91937ef659740a5ddd8e6056c32f003651a600e';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly'];assert re.findall(r'^theorem (\w+)',s,re.M)==['constructor_cuts']
a=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('def condition',1)[1].split('theorem constructor_cuts',1)[0].split(':=',1)[1];batch=a.split('  batch01 :',1)[1].split('  batch02 :',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
assert 'Fin.cons (1 : V)' in s and '(gap tau inner value negative : V)' in s
f=(d/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/ForwardWitness38.lean').read_text();assert all(f'let w{j} : S :=' in f for j in (18,19,20))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'forward second AllCuts batch source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
