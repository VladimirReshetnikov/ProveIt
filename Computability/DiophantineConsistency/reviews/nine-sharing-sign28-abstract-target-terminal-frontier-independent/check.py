#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-abstract-target-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-abstract-target-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='b753a68049b19f3b093e007c3656c71585155f0efb23f4f1710c3bb4b7c9e91a' and sha(A/'outer-result.json')=='35c41e8986836a7859240feef5c840911ea782b6a1867a650467ae1a862d27de';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(5061,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1312 and s['runner_sha256']==sha(P/'run.py')=='d2afdfdcd2e8b35e4e99ce235f32684172e58b0cca6d333c3295015140662f75';names=['Sign28AbstractTarget'];objects=['f43b24c0dcde1ad6aa17fc642d289ec64d82e1775bafbc5c43e0eb7fde2effec'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28CurrentConsIff','2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in [('Sign28AbstractTarget.transfer','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-abstract-target-prelaunch-frontier-independent/check.py';assert sha(review)=='b52dc1acf5c7d2e688a4784cbb5a820ef2c143bc14e4a48317e0e6d4aa2c53bb'
for survey,h in [('partial-survey.py','462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e'),('union-survey.py','a2f88678529dfef74f0f93aebf5b9e62ee0830842571089b48e91f646b91ab12')]:
 p=P/survey;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':5061,'stages':1,'guard_slots':100,'overlay_links':1312,'scope':'conditional abstract target transfer only in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
