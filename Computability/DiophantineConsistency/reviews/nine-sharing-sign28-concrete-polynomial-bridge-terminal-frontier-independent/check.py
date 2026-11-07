#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-concrete-polynomial-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-concrete-polynomial-bridge-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='5c3002da39f06fae2f80f44416073484212d1c6f9cf1ad2678c2021c68068847' and sha(A/'outer-result.json')=='dfa26c492f90fae46e4650b6da7b613adf5d6258d01a4dd3c60863ea4b4c773a';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(17666,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1325 and s['runner_sha256']==sha(P/'run.py')=='7dad3d64d33e2a337db76ac23b403af7550d56417c95741048cce505837bd4c9';names=['Sign28DirectPolynomialBridge'];objects=['211972881dab16d1bb9be9c457b18a0e48b698be5199bdf2918d781d5e06ab07'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==200
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28ExpressionEquivalence','cd7e2c61561f59a2fa420c1968f9256accdd3b283f332a8993ec6b6bbffc9294') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 for mod,h in [('GenericPolynomialBridgeTransport','235092c6b941bffeb66e9d1f315e080436c7bc2e1fa77a5144e7889581b0895b'),('Sign31DirectPolynomialBridge','85ee7b7c99ca2160163806ac7689f9ff554316a0245a83701d0bb5c13ae1625f')]:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in [('Sign28DirectIPRA.polynomialBridge','[propext, Classical.choice, Quot.sound]')]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-concrete-polynomial-bridge-prelaunch-frontier-independent/check.py';assert sha(review)=='898f5bf2d81121aa9b733f564551a41fbf6fafbca746e8a3a20af02f85437d20'
for survey,h in [('provider-union-survey.py','a7ff6855168e8ded090d1e9de7a97aad87ca595c60984bb7436c2141bf999d89')]:
 p=P/survey;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=60)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':17666,'stages':1,'guard_slots':200,'overlay_links':1325,'scope':'concrete sign28 PolynomialBridge only; endpoint assembly separate; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
