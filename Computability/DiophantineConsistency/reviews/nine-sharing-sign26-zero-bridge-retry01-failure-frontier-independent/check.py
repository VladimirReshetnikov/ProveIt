#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-bridge-retry01';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-zero-bridge-retry01-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='c84ae9000b6e76203e4bf3115b07d6cda73c861e04783717f9617e7f7736a45f' and H(A/'outer-result.json')=='ecbbe9aec097e6a6536f21aec8f9d128c9e4df9ebedfeb310154889b530d9306';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(72853,1) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==3 and len(s['overlay_links'])==1068 and s['runner_sha256']==H(P/'run.py')=='201f274c9b168abd0f1be634089b8635da19019d215486727f851a240e843aa9';names=['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseGap'];objs=['bab579d30c0660b53eeddfe16f962a5fca592ac6b0f4b2840cfa1e7c01cb344c','1a0a69aeca1cdb04ce797f5167e076fe23464a6b0aca419185d28997d101fc5e',None];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign26RemainingCuts01':'a11be98035c1120febed4df1ed0c95b72af6801572d94ea7ede15d50d99b8f32','Sign26SeedGap':'23e9375c793b42a99d4505557fa98c4aafbf633c7a631b047662640138a245c3',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==[100,150,100][i]
 if obj:assert r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean')
 else:assert 'object_sha256' not in r and not (O/'lib/DiophantineConsistency'/f'{n}.olean').exists()
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==(1 if i==2 and phase=='compile' else 0) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split())
 if i==0:
  assert log.count('warning:')==2 and log.count('linter.unusedSectionVars')==2
  for th in ['lift_drop','drop_lift']:assert f"'DiophantineConsistency.Sign26ZeroBridge.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
 elif i==1:
  assert 'warning:' not in log and "'DiophantineConsistency.Sign26ZeroBridge.old_rows' depends on axioms: [propext]" in log and "'DiophantineConsistency.Sign26ZeroBridge.forward' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
 else:
  assert 'error: Type mismatch' in log and 'After simplification' in log and 'v 20, v 21, gap, v 22' in log and "'DiophantineConsistency.Sign26ZeroBridge.reverseGap' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]" in log
assert len(m)==4 and not (O/'lib/DiophantineConsistency/Sign26ReverseBridgeRetry.olean').exists()
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-zero-bridge-retry01-prelaunch-frontier-independent/check.py';assert H(pre)=='134238c47352f6f7b29b901d7c072d3f43c5a7ee499b91acc27234c8f7eb9a03';up=D/'reviews/nine-sharing-sign26-remaining-cuts-terminal-frontier-independent/check.py';assert H(up)=='dfa5e871926f26c7ef693eeb86d561892432cd3219e2dfdcd296745ac969e09a';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':72853,'successful_stages':2,'failed_stage':'reverseGap','guards':350,'links':1068,'scope':'forward compiled; helper type mismatch with unreduced vector applications and sorryAx, reverse stage unrun'},sort_keys=True,indent=2))
