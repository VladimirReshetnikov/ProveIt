#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint31-41-e-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint31-41-e-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='7c3b073d44aec0d7966da9e8837ddd7fb8463962ca23501fff914447e5d741b2' and H(A/'outer-terminal-author-record.json')=='5422aff19b474f436f5d346483bc42f6a846b2e0efe28749cfc608eeacb68841';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(26354,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1140 and s['runner_sha256']==H(P/'run.py')=='6221d32b9819cd10d90c1b1ec3e913cc042d482b1391a3e55e0ec9c1201c9ba8';names=['Sign33MacroEValue','Sign33MacroEPath'];objs=['b7a027039ded05a62cbb1d1dc8ff47073efca1ee11e4fbf93b0b7ae357655f61','f0d20d5e99a1cc87d50c2a735c28ab5e74cdbc703c99252f00ced54a9d5d2492'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroDPath':'6fd0f837045b66a69f7b6c5b00b643c6295ec9b81f1f10e18b9118739e51b2ac','Sign33MacroDependentE':'cece31436221e187bb90f018ee6a62951416076114a42fc91e49832acc657038','Sign33MacroJValue':'316f405c2a71847e61ac459758aa7d201f122e505357bbcac240c22763b8df07','Sign33MacroLive18Group04':'05ef726ab4c0aecb12d36ba7a0309a8875e335a387ebf4ea0810572beb9df0ec','Sign33MacroPrefixInputsB':'1fa27bad80c2a5df777dd57235777d762bc4e7018ab9b830eb447467dc300ba8','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[300,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointE.path31_34' does not depend on any axioms" in log
 for th in ([['d30_i_value','d31_E_value'],['lookup31_34','d41_E_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointE.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint31-41-e-prelaunch-frontier-independent/check.py';assert H(pre)=='f7a9a8fb9b1f83e5f79ae636a7103c488aac7306e3e3a392a04fe633d10b5b57';up=D/'reviews/nine-seed33-jones-checkpoint30-41-d-terminal-frontier-independent/check.py';assert H(up)=='fa5394913755ce7df8c8d4d5ab5af007546eb24a703e9a042540f939da9d6185';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':26354,'stages':2,'guards':450,'links':1140,'scope':'E values d31/d41 and d31→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
