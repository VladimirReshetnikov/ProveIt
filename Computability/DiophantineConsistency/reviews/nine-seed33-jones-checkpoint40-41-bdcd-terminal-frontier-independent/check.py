#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint40-41-bdcd-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint40-41-bdcd-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='ec156fe25e18be97108b8513b35fd4cd26f90cf44c901ee02837d9e1aef418a8' and H(A/'outer-terminal-author-record.json')=='d934850469000895575f30bf2c30ee94a6fbf0e09d85a4bd8762511df76c5604';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(45194,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1159 and s['runner_sha256']==H(P/'run.py')=='c76c3c5a58ce51c690865bb09fbf62e249dc4bd24157a36cccdb052c0f2e1b7a';names=['Sign33MacroBdCdPaths','Sign33MacroBdValue','Sign33MacroCdValue'];objs=['3efb18f2926eaf8bb8db4951421189d65330e749a0340d45d3f20828adda6edd','1e84cea9c16f32e1d5d8932eb127d763aadf2feb515f4fee4c9b8200dede45a5','9e333cf5e24bae7952bc4c9c7c6a81c7d444ebe83f3c4819e92d0e3e78e94cf4'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroV1Value':'e46eb589fdd00385f74916f8328d763280b54b5222d2bad44871385fca92a817','Sign33MacroCheckpoint27to34':'66446b5c0f059d25fdf94807876ff8de0c52b3e12957287a628db974556ee7fb','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d','Sign33MacroDependentBdCd':'9a4cb929d4d26042fca68d900cad0442893b67bc37b17cc2c57e1edad9c88106',names[0]:objs[0],names[1]:objs[1]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[200,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ([['lookup39_41','lookup40_41','d41_C_value'],['d40_Bd_value'],['d41_Cd_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointBdCd.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint40-41-bdcd-prelaunch-frontier-independent/check.py';assert H(pre)=='364eefb7472893fe65ee5373a2c91dadebe19caacbeec6b6ec6e62170240deca';up=D/'reviews/nine-seed33-jones-checkpoint38-39-v-terminal-frontier-independent/check.py';assert H(up)=='ae37ffb06bd358cec3d3462647d602d89528600cccecf134927d50c37f9b221b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':45194,'stages':3,'guards':450,'links':1159,'scope':'Bd d40/Cd d41 and supporting lookups only; no full output semantics'},sort_keys=True,indent=2))
