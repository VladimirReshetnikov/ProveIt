#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-coordinate-recovery-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign25-coordinate-recovery-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='0201fd4fbd43dba361fbcc76c89f7a3bc95722ff1cf5edbaa042b2fc60392e78' and H(A/'outer-result.json')=='245953e3a7b9e670ac1328b4a03e96049c8ee1a26ab72bb8ae11cb1b24881d74';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'],o['state_sha256'])==(77733,0,H(A/'state.json'))
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1064 and s['runner_sha256']==H(P/'run.py')=='3b942630630747fad1a75990b1a4168944f6f6d73066a860160442bc15caaa00';names=['Sign25CoordinateRecover','Sign25CoordinateDrop'];objs=['f2879f2237cfafbfdd67cab6548f672102d9ec916c6c950d535e6566809800eb','da0b43ba89a71147382c9e3018f9147618f16bac72f5e57f2e6daac8d3702e51'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign25RemainingCuts01':'a7c35d01deeed7d73e3d584b8a8ab2b2bd0e27f00f859548fd1a5586ebc1065e',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']==o['logs'][f'{n}-{phase}.txt']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log;th=['ell_coordinate','lift_drop'][i];assert f"'DiophantineConsistency.Sign25CoordinateRecover.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-sharing-sign25-coordinate-recovery-prelaunch-frontier-independent/check.py';assert H(pre)=='4194ad47d91c4bc6278b5e850f3476e02199eceb3aabe84de23be781a98dea8a';up=D/'reviews/nine-sharing-sign25-remaining-cuts-terminal-frontier-independent/check.py';assert H(up)=='8d992e71b6a1982c205deea43b8a3e74002c5750f2e7231da53f04f5dcf3b3f0';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':77733,'stages':2,'guards':200,'links':1064,'scope':'old-zero product-coordinate recovery and lift/drop only; no full bridge'},sort_keys=True,indent=2))
