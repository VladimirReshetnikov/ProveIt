#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'ModelEquivalence85To86.lean').read_text()
for t in ('PositiveMap85To86Draft.positive_map','FreshMap86To85Draft.positive_map','(hbeta : 0<beta)','P72Root.cast_port p 0','P85QcubeGraph.graph p','P86ResidueGraph.graph p'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-85-to-86-positive-map-draft','ordinary14-86-to-85-fresh-map-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'ModelEquivalence85To86.lean',D/'research/ordinary14-85-to-86-positive-map-draft/PositiveMap85To86.lean',D/'research/ordinary14-86-to-85-fresh-map-draft/FreshMap86To85.lean']
print(json.dumps({'scope':'source/interface inventory and draft receipt replays; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
