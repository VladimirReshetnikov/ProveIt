#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'QCubeSize.lean').read_text()
for t in ('(hbeta : 0<beta)','(hJ : 0<v 0)','(hs : 0<v 7)','8≤AuxGraphNormClientDraft.Y','mul_le_mul hq hq2','pos_iff_one_le.mp hprod'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for beta in range(1,9):
 for j in range(1,9):
  for ss in range(1,9):
   q=1+j*beta; Y=q*q*q*ss;assert q>=2 and Y>=8
assert (1+1*1)**3*1==8
p=D/'research/ordinary14-aux-graph-norm-client-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'QCubeSize.lean',p/'GraphNormClient.lean']
print(json.dumps({'scope':'source interface, finite size controls and dependency receipt replay; no Lean invocation','finite_controls':512,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
