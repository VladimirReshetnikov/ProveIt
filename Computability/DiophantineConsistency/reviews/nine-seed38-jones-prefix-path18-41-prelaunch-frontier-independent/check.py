#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-path18-41-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'964007b336c0b7b38bf49c4ec0f4b98c837ac7cfaa75ee880e4a49fca13b06b8','provider_preflight.py':'6308b46eb6c03fa54cd13c1fc5d0ea1635ef56f84aaf8daea715ba1a94d9f411','source-manifest.json':'8cdfc79d3c7abbf76cb60500ac043354524a04e8c18a09a66aefc7acfd041347','src/DiophantineConsistency/Norm38MacroPath18to41.lean':'2dff4ff4b5b7b8bdeb10a03410b51857a47d50c966efcaa0d4fdb98da30e31bb'}.items():assert sha(p/n)==h
s=(p/'src/DiophantineConsistency/Norm38MacroPath18to41.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='2dff4ff4b5b7b8bdeb10a03410b51857a47d50c966efcaa0d4fdb98da30e31bb';assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.Norm38MacroPath18to34'];assert re.findall(r'^theorem (\w+)',s,re.M)==['path18_41','lookup18_41'];assert re.findall(r'^#print axioms (\w+)',s,re.M)==['path18_41','lookup18_41']
theorem=s.split('theorem path18_41',1)[1].split('theorem lookup18_41',1)[0];assert 'PrefixPath d18 d41' in theorem and theorem.count('.castSucc')==23 and theorem.count('PrefixPath.step')==7 and theorem.count('Dag.snoc')==7 and 'path18_34' in theorem
lookup=s.split('theorem lookup18_41',1)[1].split('#print',1)[0];assert 'd41.values a ' in lookup and '= d18.values a i' in lookup and lookup.count('.castSucc')==23 and 'lookup path18_41 a i' in lookup
nodes=(d/'research/nine-seed38-jones-named-prefix-check/src/DiophantineConsistency/Norm38MacroPrefixes.lean').read_text()
for j in range(35,42):assert f'def d{j} : Dag {j} := .snoc d{j-1} ' in nodes

r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'concrete twenty-three-snoc path source and point-provider review; no Lean replay'},indent=2,sort_keys=True))
