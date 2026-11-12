#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2]; H=Path(__file__).resolve().parent
s=(H/'SignedMainNorm.lean').read_text()
for x in ('fields84 p v hz','MainNorm84Draft.shared_main p','AuxGraphNormClientDraft.main_eval p beta v hport','scaled_signed_root',' ∨\n','(hs : 0<v 7)') :assert x in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for name in ('ordinary14-84-main-norm-client-draft','ordinary14-scaled-signed-root-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[H/'SignedMainNorm.lean',D/'research/ordinary14-84-main-norm-client-draft/MainNormClient.lean',D/'research/ordinary14-scaled-signed-root-draft/SignedScaledRoot.lean']
print(json.dumps({'scope':'source/interface inventory and dependency replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
