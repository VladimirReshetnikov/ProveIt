#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'OwnZeroMainBalance.lean').read_text()
for t in ('rank_of_84_zero','main_norm_and_balance','(hv 1) (hv 6) hz','add_pos (hv 9) (hv 10)','(hv 7) hY hk hR hz','(hY : 8≤'):assert t in s
for t in ('hbeta','hK','hMC','hMF'): assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
for n in ('ordinary14-84-natural-rank-draft','ordinary14-84-main-balance-draft'):
 p=D/'research'/n;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),n
paths=[P/'OwnZeroMainBalance.lean',D/'research/ordinary14-84-natural-rank-draft/NaturalRank.lean',D/'research/ordinary14-84-main-balance-draft/MainBalance.lean']
print(json.dumps({'scope':'source/interface inventory and two dependency receipt replays only; no Lean invocation','sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
