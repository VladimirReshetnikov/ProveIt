#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'ModelEquivalence.lean').read_text()
for t in ('ModelMap84To85Draft.positive_map','ModelMap85To84Draft.positive_map','(hbeta46 : 46≤beta)','(ht : 4≤t)','(hradix : beta=Exp.exp t-1)','P84QcubeGraph.graph p','P85QcubeGraph.graph p'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-to-85-model-map-draft','ordinary14-85-to-84-model-map-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'ModelEquivalence.lean',D/'research/ordinary14-84-to-85-model-map-draft/ModelMap.lean',D/'research/ordinary14-85-to-84-model-map-draft/ModelMap85To84.lean']
print(json.dumps({'scope':'source/interface inventory and two draft receipt replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
