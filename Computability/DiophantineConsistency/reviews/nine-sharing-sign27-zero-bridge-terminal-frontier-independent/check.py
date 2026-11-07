#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign27-zero-bridge-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign27-zero-bridge-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='9ba674fff2496dc106de2b59915c3e6d1912d4d51f831c6c1901c12d126fe35b' and H(A/'outer-result.json')=='41b8b762e54985e48d3273ad5a6883b9d01fac4f51e0dd421434b2cb7625e432';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(59520,0) and o['retained_state_sha256']==H(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1067 and s['runner_sha256']==H(P/'run.py')=='8b64a461f46253673b16e5e67d3e1df636bb2d37d33284201d638780c26a64fc';names=['Sign27CoordinateDrop','Sign27ForwardBridge','Sign27ReverseBridge'];objs=['cab3f81dd8b9415789c247d014974c601ddc23d326a05f25c81b245dd3149dfb','156358ff65376b62600e83fb034e64c1f2d20f35b43acd8223902486217be0b5','f2211f087d41951bd6d8724e72c14e11273b98df7d5292d7ace3dd750a11b029'];ths=[[('lift_drop','[propext, Classical.choice, Quot.sound]'),('drop_lift','[propext, Classical.choice, Quot.sound]')],[('old_rows','[propext]'),('forward','[propext, Classical.choice, Quot.sound]')],[('new_rows','[propext]'),('backward','[propext, Classical.choice, Quot.sound]')]];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 direct=[[('Sign27RemainingCuts01','d2a7b369c4eec8c484cf88bf0aa1a1d071d1b450c1e93be3e17da8213029eb4d')],[('Sign27CoordinateDrop',objs[0]),('Sign27AffectedCuts','f78aed3abe3e52e67a623c6e817685d35103d106cbb057183ed92929faa2115b')],[('Sign27ForwardBridge',objs[1]),('Sign27SeedRootRecovery','27b27811d4aaf0588408034bed6405e76b500ff733794fd59a037aea854a0305')]][i]
 for mod,h in direct:
  v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th,ax in ths[i]:assert f"'DiophantineConsistency.Sign27ZeroBridge.{th}' depends on axioms: {ax}" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign27-zero-bridge-prelaunch-frontier-independent/check.py';assert H(pre)=='8d5ea3365832da7bc1d8519dc78c4555616f1ab5b6aa0b0afb3b5c8bf774c862'
for n,h in [('nine-sharing-sign27-remaining-cuts-terminal-frontier-independent','cc266749f6c4c4cb91534ef7cfbb6287af6a8a7c507b59251084d7cf2fee99ed'),('nine-sharing-sign27-affected-cuts-terminal-frontier-independent','b21ebe8973098c99d81abfa645d3468398fe99872948811da472b5a251fd20b3'),('nine-sharing-sign27-seed-root-recovery-terminal-frontier-independent','b810905848e81ee03d7e7fda162d1c454a05ae77ed5be77277b9b6bd44a8699c')]:
 p=D/'reviews'/n/'check.py';assert H(p)==h;subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,check=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':59520,'stages':3,'guards':400,'links':1067,'scope':'forward sign27 to sign28 zero, reverse with existential predecessor and both coordinate equations; no endpoint'},sort_keys=True,indent=2))
