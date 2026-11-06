#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-squares-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'56531df3f1e334f21993b9dfead540de86349719ab5ebac99495bc6b0d57751e','source-manifest.json':'8180e5a7cb0ea8b093ac18e0cafd652065073c2542dcad07f9757bafde786666','src/DiophantineConsistency/SharingSign33Squares.lean':'da2b90143d1452756d9ea24612126e06cf38ae93a9c22cbab4e322d19ac5b190'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/SharingSign33Squares.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='da2b90143d1452756d9ea24612126e06cf38ae93a9c22cbab4e322d19ac5b190'
assert re.findall(r'^import ([\w.]+)$',s,re.M)==rows[0]['imports']==['DiophantineConsistency.SharingSeed33Syntax'];assert re.findall(r'^theorem (\w+)',s,re.M)==['squareSum_nonneg','squareSum_zero_iff','square_syntax','seed_zero_iff_residuals'];assert len(re.findall(r'^#print axioms ',s,re.M))==3
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled model-difference-ring sum of squares iff; no Lean run'},sort_keys=True,indent=2))
