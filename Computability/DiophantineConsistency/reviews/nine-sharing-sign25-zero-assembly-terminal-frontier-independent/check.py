#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-zero-assembly-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-zero-assembly-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='e858743ad98667e6c86ea10e63c57f1d055c8e39a6711de4bc1b4c326195b8eb' and H(A/'outer-result.json')=='ea68c4ec656ba359a454dd4f63232022ccf1cb5bc9c2d94764c819e0dd7292eb';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(39074,0,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1064 and s['runner_sha256']==H(P/'run.py')=='5fc0b256fec537ac0524c46d253d54fa120bf15b464516fa28c744e7325fa47b'
names=['Sign25CoordinateRecover','Sign25CoordinateDrop','Sign25ForwardBridge','Sign25ReverseBridge'];objs=['f2879f2237cfafbfdd67cab6548f672102d9ec916c6c950d535e6566809800eb','da0b43ba89a71147382c9e3018f9147618f16bac72f5e57f2e6daac8d3702e51','50aa9aeb28fc88152f06f755558e88ce2bcaea2d265dfd4d36021554fc9b4c60','2b7b552bfa3143958677bba12bea17e571061382058209c686bb42d60e71c9ab'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign25RemainingCuts01':'a7c35d01deeed7d73e3d584b8a8ab2b2bd0e27f00f859548fd1a5586ebc1065e',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,100,100,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 ns='Sign25CoordinateRecover' if i<2 else 'Sign25ZeroBridge';th=['ell_coordinate','lift_drop','forward','backward'][i];assert f"'DiophantineConsistency.{ns}.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
 if i>=2:
  row=['old_rows','new_rows'][i-2];assert f"'DiophantineConsistency.Sign25ZeroBridge.{row}' depends on axioms: [propext]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-zero-assembly-prelaunch-frontier-independent/check.py';assert H(pre)=='aa8a90f608bbb68002ea975761d8b70d65a4026c127303e29a8d5e41a15dde13';up=D/'reviews/nine-sharing-sign25-coordinate-recovery-terminal-frontier-independent/check.py';assert H(up)=='ff1636e4feedd55150154b198d60dbca072a1e3ab6994788069d789b818d783b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':39074,'stages':4,'guards':400,'links':1064,'scope':'pointwise product lift/drop sign25↔sign26 seed-zero bridge over IΣ₁; no existential endpoint'},sort_keys=True,indent=2))
