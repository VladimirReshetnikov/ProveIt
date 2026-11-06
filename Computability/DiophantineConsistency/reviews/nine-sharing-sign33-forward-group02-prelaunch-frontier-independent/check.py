#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'8cd66aefa123a05b1094c15605987626c8265dbc065d8649084ee9c82f602a45','provider_survey.py':'05e64723175655f4858a2b47335c45d33aefa361aa5d0275ab8cc2cb986076fa','source-manifest.json':'ecd19825e863ab0fbaff64b5d02a145eb22b640f09cd5272b5cac832a646e1cc','src/DiophantineConsistency/Sign33ForwardGroup02.lean':'0e03687df38ef9718cc142c2ba0df5fe0aff6f45a98fba4de8157af9de809c66'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Sign33ForwardGroup02.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='0e03687df38ef9718cc142c2ba0df5fe0aff6f45a98fba4de8157af9de809c66';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingForward33','DiophantineConsistency.Sign33ResidualAssembly'];assert re.findall(r'^theorem (\w+)',s,re.M)==['constructor_cuts']
a=(d/'research/nine-sharing-sign33-residual-assembly-check/src/DiophantineConsistency/Sign33ResidualAssembly.lean').read_text();condition=s.split('def condition',1)[1].split('theorem constructor_cuts',1)[0].split(':=',1)[1];batch=a.split('  batch02 :',1)[1].split('  batch03 :',1)[0];assert re.sub(r'\s+','',condition)==re.sub(r'\s+','',batch)
assert 'Fin.cons (1 : V)' in s and '(gap tau inner value negative : V)' in s
f=(d/'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/ForwardWitness38.lean').read_text();assert all(f'let w{j} : S :=' in f for j in (21,22,23))
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'forward third AllCuts batch source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
