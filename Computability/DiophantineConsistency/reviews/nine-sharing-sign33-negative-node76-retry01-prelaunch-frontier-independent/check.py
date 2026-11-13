#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-negative-node76-retry01';old=d/'research/nine-sharing-sign33-negative-node76-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
n='Sign33NegativeNode76';new=(p/'src/DiophantineConsistency'/f'{n}.lean').read_text();prev=(old/'src/DiophantineConsistency'/f'{n}.lean').read_text();assert sha(p/'src/DiophantineConsistency'/f'{n}.lean')=='75a9e2cbc9aae3b54c69ef488e72b24a1c531cf202715e5bf226970852e0c2dc' and sha(old/'src/DiophantineConsistency'/f'{n}.lean')=='b3aabf0b9b2510dbbb4a18e8747f48700db68b60876252e2cf4c0974360d6637'
assert prev.count('  dsimp only\n')==1 and prev.replace('  dsimp only\n','')==new
assert sha(old/'attempt01/state.json')=='134a6c8fbd060e56b15e90b839d2efd48a273ab5cf6ad7174a3a306ff057bc3a'
assert sha(p/'source-manifest.json')=='ab99a5486e7e7d77553df5eccee17d3f4dd405f7eb8c46232527fb72c75cab56' and sha(p/'run.py')=='5c4616be2faec6110e4203afdb63aefa51b75e2eaf5ff435c1b3c4d641965eac'
a=(old/'run.py').read_text().replace('nine-sharing-sign33-negative-node76-check-20261106','nine-sharing-sign33-negative-node76-retry01-20261106').replace('ce43eedb50a05a0b70d780c52bb22abc88dcec9ae2869c01f61615e539f43548','ab99a5486e7e7d77553df5eccee17d3f4dd405f7eb8c46232527fb72c75cab56');assert a==(p/'run.py').read_text()
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'targeted proof retry; no Lean replay'},indent=2,sort_keys=True))
