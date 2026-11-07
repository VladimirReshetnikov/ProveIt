#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint28-41-j-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint28-41-j-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='8ff53fc12a9ffc22ddc3ec06194beefe78d70b192f392f4b2762c6121e8f27b5' and H(A/'outer-terminal-author-record.json')=='648c014ba4d4e8c13570f17187bfea95e852a11240836aa3419e63ec247b1970';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(69236,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1131 and s['runner_sha256']==H(P/'run.py')=='36cf7a0098033d89fa13b00e73fa7d942840f8b9665997ad9945dea6114c10aa';names=['Sign33MacroJValue','Sign33MacroJPath'];objs=['316f405c2a71847e61ac459758aa7d201f122e505357bbcac240c22763b8df07','14a7e6c714d2ad44a4cf3b35c66fc2202cfa61f15c0f94762aae6802d8ef4772'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroAValue':'7fbf4ea8332abaca614384a975c891dba2553b4205e28654798898f426852f51','Sign33MacroDependentJ':'2e13b7fec88baed73ca02e1507eae18bb762990dc852e9619d02545b83abe272','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==150
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointJ.path28_34' does not depend on any axioms" in log
 for th in ([['d28_J_value'],['lookup28_34','d41_J_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointJ.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint28-41-j-prelaunch-frontier-independent/check.py';assert H(pre)=='de25645f0556d51781515b3b8ad1bf519fab3985f741779b218a97457f598867';up=D/'reviews/nine-seed33-jones-checkpoint24-27-a-terminal-frontier-independent/check.py';assert H(up)=='8d524a4ea8e64118dc49758df0eb14ba59217f3942b352cdd214870efbc82d92';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':69236,'stages':2,'guards':300,'links':1131,'scope':'J values d28/d41 and d28→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
