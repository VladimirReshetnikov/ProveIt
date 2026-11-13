#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint21-27-m-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint21-27-m-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='f5bcca49a0fecbe3cee8adc681366849f96f6236f11c91366d488282f83aa716' and H(A/'outer-terminal-author-record.json')=='28cbe7aedf930f0cf65899d33c767f5595b3829ca18198e31cc5d8086dc7daf1';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(35487,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1127 and s['runner_sha256']==H(P/'run.py')=='64b935ceec156108b125dbb4dffb6f0b6f9cf47db3b2a0ca30c801c92a26e3af';names=['Sign33MacroMPath','Sign33MacroMValue'];objs=['1818ff28d023ccf7cf66c2479cabdc78db34466f1189b3ed54217ce5cf4c8908','ae5f60f5efd022e5372faffbfc61d5033ac0afe86da416c069cfdb1c2d74beb2'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroUYValues':'1ff9ee127bf870a715bc52aab178c8fece58dfceafd6700783d4830519aa67c6','Sign33MacroDependentM':'b1dfcad99ce4808c6aa675c8c8ef7e7d842755595811b10ad29eba363d5f8862','Sign33MacroLive18Group02':'8d4d912136b18a8d46b5904d3c1d8127e5fbafc40d62ffb25ef09a63c094b004',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,200][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==0:assert "'DiophantineConsistency.Sign33MacroCheckpointM.path21_27' does not depend on any axioms" in log
 for th in ([['lookup21_27'],['d27_M_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointM.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint21-27-m-prelaunch-frontier-independent/check.py';assert H(pre)=='0b3ad30ad02cc6a81759f3d19ef8ce769be1620e27b9b2d91add8ca6c7f72abb';up=D/'reviews/nine-seed33-jones-checkpoint20-27-uy-terminal-frontier-independent/check.py';assert H(up)=='499b586380e0a79fc23fef946781ef746757d3d90ce543dc7fb80051d8051ede';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':35487,'stages':2,'guards':300,'links':1127,'scope':'d27 M with opaque d11 rank, d21→d27 lookup only; no full output semantics'},sort_keys=True,indent=2))
