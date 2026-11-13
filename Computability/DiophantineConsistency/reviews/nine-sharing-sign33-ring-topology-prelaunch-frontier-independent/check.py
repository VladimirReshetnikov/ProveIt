#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-topology-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'9df23c0ea3191ebb9f0544c59372f9a318fca36abebdd5bbf935719a4988f9f1','provider_survey.py':'f47f7fac8f3f91c274c413846d85702066d9f5d08424cc5f1772e43df69cfa5a','source-manifest.json':'798098f21b06981c84b74421cc895a0d972a677c873d5f0749a5aff5996520c1','src/DiophantineConsistency/Sign33RingTopology.lean':'74fc4a3c1c2302d3c35a23239f286cb991d3a64e823694299bae214474e2dc3f'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33RingTopology.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='74fc4a3c1c2302d3c35a23239f286cb991d3a64e823694299bae214474e2dc3f';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingTopology38'];assert re.findall(r'^theorem (\w+)',s,re.M)==['static_agrees_of_topological'];assert s.count('ringRun_agrees_of_topological gs done')==2 and '(hv i hi).symm.trans (hr i hi)' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled conditional double-topology theorem; no Lean replay'},sort_keys=True,indent=2))
