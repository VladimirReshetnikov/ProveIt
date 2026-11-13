#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group00-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'395f1d59ee4db9d1c6ac2b08747348127307b93f1259bb084e56673553539994','provider_survey.py':'d87cddf415741e06f370eef29319debd5480c3b9156a27977a564a540cb3f6b3','source-manifest.json':'56a8c7e08b34a06a96042e96b484cfaf362922c1c2060a1da6382d43422aa53d','src/DiophantineConsistency/Sign33ForwardGroup00.lean':'fa537a7a95c379533bc2e316fde45665679066eae7c07c69a799fffef4483248'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardGroup00.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='fa537a7a95c379533bc2e316fde45665679066eae7c07c69a799fffef4483248';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly'];assert re.findall(r'^theorem (\w+)',s,re.M)==['constructor_cuts']
a=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('def condition',1)[1].split('theorem constructor_cuts',1)[0].split(':=',1)[1];batch=a.split('  batch00 :',1)[1].split('  batch01 :',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
assert 'Fin.cons (1 : V)' in s and '(gap tau inner value negative : V)' in s
for j in (1,9,15,16,17):assert f'h{j} :' in s and f'({j-1} : Fin 33).succ = ({j} : Fin 34)' in s
f=(d/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/ForwardWitness38.lean').read_text();assert all(f'let w{j} : S :=' in f for j in (15,16,17))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'forward first AllCuts batch source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
