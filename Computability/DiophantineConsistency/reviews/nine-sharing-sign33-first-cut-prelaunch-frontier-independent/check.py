#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-first-cut-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'ddbf9da892239427a002e061beddbb857d4b5c17596bf12d57f29e988bd0c3ba','provider_survey.py':'60b66763bd24df531a7191a914fff34f43f0f3d5b77739e65eb03aedf9de74ba','source-manifest.json':'566811e1adabc28e03febcf502742fa9861cabeec78646586db04b609fbc5485','src/DiophantineConsistency/Sign33FirstCut.lean':'b522f8e9869714e04be8eb69eef93668b6aa6ee65f6f0e974ce8bdfb2eba5c74'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33FirstCut.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='b522f8e9869714e04be8eb69eef93668b6aa6ee65f6f0e974ce8bdfb2eba5c74';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.SharingSign33Squares'];assert re.findall(r'^theorem (\w+)',s,re.M)==['first_residual_eval','first_cut_of_seed_zero'];assert len(re.findall(r'^#print axioms ',s,re.M))==2
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled first residual cut, symbolic port cast; no Lean replay'},sort_keys=True,indent=2))
