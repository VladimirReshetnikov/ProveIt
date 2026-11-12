#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'PositiveMainBalance.lean').read_text()
for t in ('(hbeta : 0<beta)','Y_at_least_eight beta v hbeta (hv 0) (hv 7)','OwnZeroMainBalance84Draft.norm_and_balance','hport hK hMC hMF hv hY hz'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for n in ('ordinary14-84-own-zero-main-balance-draft','ordinary14-84-qcube-size-draft'):
 p=D/'research'/n;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),n
paths=[P/'PositiveMainBalance.lean',D/'research/ordinary14-84-own-zero-main-balance-draft/OwnZeroMainBalance.lean',D/'research/ordinary14-84-qcube-size-draft/QCubeSize.lean']
print(json.dumps({'scope':'source/interface inventory and two dependency receipt replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
