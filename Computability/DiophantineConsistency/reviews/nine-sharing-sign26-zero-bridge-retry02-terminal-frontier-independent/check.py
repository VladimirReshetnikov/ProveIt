#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-zero-bridge-retry02';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign26-zero-bridge-retry02-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='81cf0a60b604b75beb7516e28d91bd22128ecba3dd3e29c85e933ef7f0fedaaa' and H(A/'outer-result.json')=='a90714cbbde612a2f6caa82ada957e9f2a930b0a7f3aa7592447964482854326';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(37631,0) and o['state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1068 and s['runner_sha256']==H(P/'run.py')=='ed6519380cb2f20a94684b8fb8be55b6abe95ccfcade96c574c7024490e7940c';names=['Sign26CoordinateDrop','Sign26ForwardBridge','Sign26ReverseGap','Sign26ReverseBridgeRetry'];objs=['35734d6d2199d4759177b80c4f5ebded14901d6fcca41a2e56ee9ab5ddeb9b70','1a0a69aeca1cdb04ce797f5167e076fe23464a6b0aca419185d28997d101fc5e','73580e6b950613fe736a3a8d45b8bce205549d86346ce3de991a87359a72cadc','5332b906ba2a44d6d44e6eed8e5557d96a8a286b6d8ed0e2afa5d3df87d3e352'];ths=[[('lift_drop','[propext, Classical.choice, Quot.sound]'),('drop_lift','[propext, Classical.choice, Quot.sound]')],[('old_rows','[propext]'),('forward','[propext, Classical.choice, Quot.sound]')],[('reverseGap','[propext, Classical.choice, Quot.sound]')],[('new_rows','[propext]'),('backward','[propext, Classical.choice, Quot.sound]')]];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign26RemainingCuts01':'a11be98035c1120febed4df1ed0c95b72af6801572d94ea7ede15d50d99b8f32','Sign26SeedGap':'23e9375c793b42a99d4505557fa98c4aafbf633c7a631b047662640138a245c3',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150,100,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'sorryAx' not in log and 'error:' not in log
 if i==0:assert log.count('warning:')==2 and log.count('linter.unusedSectionVars')==2
 else:assert 'warning:' not in log
 for th,ax in ths[i]:assert f"'DiophantineConsistency.Sign26ZeroBridge.{th}' depends on axioms: {ax}" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign26-zero-bridge-retry02-prelaunch-frontier-independent/check.py';assert H(pre)=='2dbf535c59c0d06430dc828449765086f381516756f4f88631f7a43fcece374b';up=D/'reviews/nine-sharing-sign26-zero-bridge-retry01-failure-frontier-independent/check.py';assert H(up)=='2bbbc7fce0790848bf17cf527ea9be6a7780a5dc16ce97be5cdc770f2e92313f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':37631,'stages':4,'guards':450,'links':1068,'warnings':2,'scope':'sign26→27 forward zero conditional on p0/p1 casts and beta≥1; sign27→26 reverse without extra port assumptions'},sort_keys=True,indent=2))
