#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-path18-34-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'6588946cae30eea1dedf0065337ca019b9d1a8aa0850cfc1b3d6a1667fddcbd4','provider_preflight.py':'6119605628d6f6b6075ce8f93dfc190206523036d3b26c3c1f7dc49b7e1ba8e7','source-manifest.json':'070e09340b93ef5f0e7b5b61764acb9d8a1b5cb4ff3372f942f75c7723120951','src/DiophantineConsistency/Norm38MacroPath18to34.lean':'3be3ce5b6535a492ff295bcdc0a54b9e8ed7addf860e60a0eb37bb80f39a6e34'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroPath18to34.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='3be3ce5b6535a492ff295bcdc0a54b9e8ed7addf860e60a0eb37bb80f39a6e34';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroPath18to27'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path18_34','lookup18_34'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['path18_34','lookup18_34']
theorem=s.split('theorem path18_34',1)[1].split('theorem lookup18_34',1)[0];assert 'PrefixPath d18 d34' in theorem and theorem.count('.castSucc')==16 and theorem.count('PrefixPath.step')==7 and theorem.count('Dag.snoc')==7 and 'path18_27' in theorem
lookup=s.split('theorem lookup18_34',1)[1].split('#print',1)[0];assert 'd34.values a ' in lookup and '= d18.values a i' in lookup and lookup.count('.castSucc')==16 and 'lookup path18_34 a i' in lookup
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(28,35):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes
old=(p/'observations/setup01/provider_preflight.py').read_text();new=(p/'provider_preflight.py').read_text();assert old.replace("obj = base / 'Norm38MacroPath18to34.olean'","obj = base / 'Norm38MacroPath18to27.olean'")==new
oldrun=(p/'observations/setup01/run.py').read_text();newrun=(p/'run.py').read_text();assert oldrun.replace('80147947b8d690a16dbb84170a018c764f080f3e524d9ac6307d1f7a8c4702a5','6119605628d6f6b6075ce8f93dfc190206523036d3b26c3c1f7dc49b7e1ba8e7')==newrun
history=json.loads((p/'observations/setup01/author-record.json').read_text());assert (history['preflight_session'],history['preflight_exit'],history['survey_diagnostic_session'],history['survey_diagnostic_exit'],history['error'])==(33244,1,44669,1,'first-prefix provider')

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'concrete sixteen-snoc path source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
