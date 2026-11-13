#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
s=(P/'ModelEquivalence78To75.lean').read_text()
for t in ('namespace DiophantineConsistency.ModelEquivalence7875Draft','theorem zero_iff ','theorem zero_iff_natural_ports','(hbeta : (p 0 : DiffRing V)=ι beta)','(hb : 0<beta)','(hv : ∀ j, 0<v j)','Model75To78Draft.zero_78_of_75_zero p beta v hbeta hb hv','Model78To75Draft.zero_of_78_zero p v','P72Root.cast_port p 0'):
 assert t in s,t
replayed=[]
for name in ('ordinary14-75-to-78-model-map-draft','ordinary14-78-to-75-model-map-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
 assert r.stdout==(p/'observation.json').read_bytes() and not r.stderr;replayed.append(name)
paths=[P/'ModelEquivalence78To75.lean',D/'research/ordinary14-75-to-78-model-map-draft/Model75To78.lean',D/'research/ordinary14-78-to-75-model-map-draft/Model78To75.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source-interface and dependency receipt replay; no Lean or model theorem','files':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},'dependency_receipts_replayed':replayed},sort_keys=True,indent=2))
