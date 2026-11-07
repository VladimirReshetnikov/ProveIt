#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint35-41-i-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint35-41-i-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='106457343a64e97a86327ac879a4b23aaca16ca8b24f32809f7fa17c48602f23' and H(A/'outer-terminal-author-record.json')=='ec33843473c7c7638a45108f74cb064173d2e318125bb24437b5811895761fd2';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(66538,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1148 and s['runner_sha256']==H(P/'run.py')=='a05af617176c4af55661bd08d9a14229094a773b9f8e2b67dcc3ce08cb5de72e';names=['Sign33MacroIValue','Sign33MacroIPath'];objs=['de33e3763b4604ab639d323ba65f628a21ff86c8f42ca5522fcd9003fd3fdcce','b23a629ef3d1a20513930714517fec8895f9f43e228efbe77123e06617a3d7d2'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroHPath':'6a2b366e725ff74521b0334321b1ff94a5266088edbc1c77b533b26eff8253d9','Sign33MacroDependentI':'9c2f73b4a8d97fe02e9058bc6edb825998a8a6a4b955e5cb72177b3cca92bc0b',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointI.path35_41' does not depend on any axioms" in log
 for th in ([['d35_I_value'],['lookup35_41','d41_I_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointI.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint35-41-i-prelaunch-frontier-independent/check.py';assert H(pre)=='378f3fe6891ac03834307558bebb8b4b30785f621fe0696d371e3d56122bd521';up=D/'reviews/nine-seed33-jones-checkpoint34-41-h-terminal-frontier-independent/check.py';assert H(up)=='ee494cb033aee437a66bd900f7b29f4b8aaff2600d0d03e3e82a7a8c65f6e9b1';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':66538,'stages':2,'guards':250,'links':1148,'scope':'I values d35/d41 and d35→d41 path only; no full output semantics'},sort_keys=True,indent=2))
