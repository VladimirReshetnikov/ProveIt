#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-expression-equivalence-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-expression-equivalence-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='71e455d74fe8d8eca582c94f4d75951435191c0e9a4d156266ec660e743c9e34' and sha(A/'outer-result.json')=='9865b6725c672f79d03c5b1e07a1a2803f2cb0183bbea850452d70a14c5cc96b';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(92816,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1321 and s['runner_sha256']==sha(P/'run.py')=='97e4c2e0f5a97f7d3727c49ff6abf9ebca2820b1188bd24afb77e55e4448330a';names=['Sign28ExpressionEquivalence'];objects=['cd7e2c61561f59a2fa420c1968f9256accdd3b283f332a8993ec6b6bbffc9294'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28CurrentConsIff','2f7b33d5954dbc16bc528c98a3758954232304ad23f1121366881e307d74100b') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for mod,h in [('Sign28CurrentExpressionEval','2992d47b5eb75108840295f5461f5e804359bc602c7cde75908e5f2189cdc68f'),('Sign31CurrentExpressionEval','eedb576a31f8255f9b556f5edb67e4e0631ede9a19b744be502f38fb8a7e60be')]:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in [('Sign28ExpressionEquivalence.zero_exists_iff','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-expression-equivalence-prelaunch-frontier-independent/check.py';assert sha(review)=='5b9e8b73749557f55bfa6a6836abacf23c449b14ba12484c4be9e143ef822fe2'
for survey,h in [('partial-survey.py','462acee066ec0a45fb30b682cc7d435a0b4b1414b9f8129c6f326ca3049ded8e'),('sign31-survey.py','4e701dcddcb49d7f7fa902391e93e6ad45d1247b18051600cc7dfae7def894d4')]:
 p=P/survey;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':92816,'stages':1,'guard_slots':200,'overlay_links':1321,'scope':'Fin28/Fin31 current direct-expression zero-existence iff only in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
