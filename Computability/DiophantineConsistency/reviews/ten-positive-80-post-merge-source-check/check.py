#!/usr/bin/env python3
"""Recheck the 127 replay source pins and fixed evidence after the merge."""
from hashlib import sha256
from pathlib import Path
import json,subprocess
H=Path(__file__).resolve().parent;D=H.parents[1]
PLAN=D/'reviews/ten-positive-80-127-rebuild-preflight/observations/attempt01.json'
RUN=D/'research/ten-positive-80-coherent-rebuild/observations/attempt04/result.json'
OUTER=D/'research/ten-positive-80-coherent-rebuild/observations/outer-attempt04/terminal.json'
CLOSURE=D/'reviews/ten-positive-80-coherent-rebuilt-closure/observations/attempt01/result.json'
OUT=H/'observations/attempt01.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(not OUT.exists(),'output exists')
expected={PLAN:'cd224b6f17f9cd3cd08cf3a9e84923c1de9edbb635f6969cd4e1991e009b7e3a',
 RUN:'e1ccee0f9c5fdc14cde89368925cb56f41d6acbe5c89a41c9e2bab798184582b',
 OUTER:'6d385d6ced237bedd626daabc047691d49a5314f399b941d3a09c1f71cc9aa96',
 CLOSURE:'75d4cf43ed4d716b15a13536be5a4cbba96ad03e2249aba7acdc7ace30892276'}
for p,h in expected.items():need(sha(p)==h,'pinned evidence drift '+str(p))
plan=json.loads(PLAN.read_text());run=json.loads(RUN.read_text());outer=json.loads(OUTER.read_text());closure=json.loads(CLOSURE.read_text())
need(run['status']=='PASS' and outer['exit']==0 and closure['status']=='PASS','prior status')
need(outer['runner_sha256_before']==outer['runner_sha256_after']=='1956a0831c4dc93c5f30ff578ec6e7731c7d56f4be695d3ee8a7c4681a982298','runner mismatch')
for p,h in plan['inputs'].items():need(Path(p).is_file() and sha(p)==h,'plan evidence drift '+p)
sources={}
for n,z in plan['sources'].items():
 p=Path(z['source']);need(p.is_file() and sha(p)==z['sha256'],'source drift '+n);sources[n]={'path':str(p),'sha256':z['sha256']}
for p,h in run['inputs'].items():need(Path(p).is_file() and sha(p)==h,'replay input drift '+p)
head=subprocess.run(['git','rev-parse','HEAD'],cwd=D,capture_output=True,text=True,check=True).stdout.strip()
result={'status':'PASS','head':head,'sources':sources,'plan_inputs':plan['inputs'],
 'evidence':{str(p):sha(p) for p in expected},'replay_inputs':run['inputs'],
 'scope':'current 127 source and fixed evidence bytes only; not full workspace diff, Lean replay, external binding or inherited ancestry'}
OUT.parent.mkdir(parents=True,exist_ok=True);OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','head':head,'sources':len(sources),'sha256':sha(OUT)},sort_keys=True))
