#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-zero-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-zero-bridge-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='fa1c8aeef56d0ca8dba24389602f4862518cc5589ac58d51ca0984fbea25fc6b' and sha(A/'outer-result.json')=='fad5f09f03d0cbc2a1b4a3d68a5c19ba83bbbe816c9116e909bd997a904f68f1';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(82745,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1064 and s['runner_sha256']==sha(P/'run.py')=='9b03c17fc52f1dfd8794efb70756cebe3ae445cc241f6f88f98cc5ca57659051';names=['Sign31CoordinateRecover','Sign31CoordinateDrop','Sign31ForwardBridge','Sign31ReverseBridge'];objects=['d00771b06fc0f94087d8d5a6820d6ee4edf596cad83aa952d1b6d03516eb1eab','24d69ba4a8d930d5f826c0bf08865a04fa3bfb9ce04ff054aa5fdbdf218d097b','2210a6c6d3dc9c3db1da92bad76a275521d54201707af21759be256c8b8c364a','4ed14ddee585ff6b50922b908ca42e6a2205d965c090722e6d129e8e7d571603'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign31RemainingCuts01','20c42c47ebfe30151e36dc51cfbfd2b4a993d4fd633eba6b7f7021570e033b9e') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ([('Sign31CoordinateRecover.f2_coordinate','[propext, Classical.choice, Quot.sound]')],[('Sign31CoordinateRecover.lift_drop','[propext, Classical.choice, Quot.sound]')],[('Sign31ZeroBridge.old_rows','[propext]'),('Sign31ZeroBridge.forward','[propext, Classical.choice, Quot.sound]')],[('Sign31ZeroBridge.new_rows','[propext]'),('Sign31ZeroBridge.backward','[propext, Classical.choice, Quot.sound]')])[i]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for rel,h in [('nine-sharing-sign31-zero-bridge-prelaunch-frontier-independent/check.py','a903ff0a285af2bbb3d784ba46a2c64e5410492188138e0cc0fdd47f23b0b933'),('nine-sharing-sign31-remaining-cuts-terminal-frontier-independent/check.py','9c4e858fd24adb3d6737f18fb1f354d717eb2ef4cd5b9496c1c4ea1eddd1a77e')]:
 p=D/'reviews'/rel;assert sha(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':82745,'stages':4,'guard_slots':400,'overlay_links':1064,'scope':'same symbolic ports; sign31 forward lift and sign32 reverse drop in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
