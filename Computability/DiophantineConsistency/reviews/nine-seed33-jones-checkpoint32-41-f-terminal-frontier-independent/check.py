#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint32-41-f-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint32-41-f-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='498f5764cb2ea025836aafbadf672736ae702d404df6c95ee209fef76bb75a14' and H(A/'outer-terminal-author-record.json')=='eb8e84da061031176b5089845ea37c2d86f8ecfc04f275a55995ae76de771118';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(64626,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1142 and s['runner_sha256']==H(P/'run.py')=='79d9930e4240da3594b096d870534b98f01678035a6b30357733e66b4dd1193a';names=['Sign33MacroFValue','Sign33MacroFPath'];objs=['b4ce86615456081e5439993fc6e3f43fbf4b751234a4b6831c854bfb2e0feb7c','0986f9676c54a98490a592bd444006c7ad597044f44135cee49664aafd058b39'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroEPath':'f0d20d5e99a1cc87d50c2a735c28ab5e74cdbc703c99252f00ced54a9d5d2492','Sign33MacroDependentF':'e844c55fd2abd3abb4ca61dedbdc1d194a82a9a6e61cad757ee8b1879fa891c6','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[150,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointF.path32_34' does not depend on any axioms" in log
 for th in ([['d31_A_from_d29','d32_F_value'],['lookup32_34','d41_F_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointF.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint32-41-f-prelaunch-frontier-independent/check.py';assert H(pre)=='330709a654dd564a6656749087c82d0b80f7d33a8ecfc0de73bf89c195556bbb';up=D/'reviews/nine-seed33-jones-checkpoint31-41-e-terminal-frontier-independent/check.py';assert H(up)=='84c51316ab51223a4a30dc48d0e2ddc059d2119185aebc2e2ee203b2790ec426';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':64626,'stages':2,'guards':300,'links':1142,'scope':'F values d32/d41 and d32→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
