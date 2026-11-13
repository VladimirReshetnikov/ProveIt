#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint36-41-a0-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint36-41-a0-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='8c454a84dad8d55aef95dbb15b77680853a692fef1cc41e773832d4b6a7a4e69' and H(A/'outer-terminal-author-record.json')=='9fdcf3d913cfa964ee5a378ea8b53ac2dae03eaec0050f0287a275e7c909dba2';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(4154,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1152 and s['runner_sha256']==H(P/'run.py')=='e0665fb48b916a29fc1b9d722256d46052e6bcf8e51bbd52a262a076d52d4fa8';names=['Sign33MacroPKPaths','Sign33MacroA0Value','Sign33MacroA0Path'];objs=['7054d5191899e0a509d8d8b1a10dc3b985b1f3c139ce1de41af7121994b2c4da','e43bca29208f0be8a5348de884b1624fb4e899a7f8b58082e096510283d3e838','8e746bd55046055067b7dad1e5f10ff22063c186b7ed4e2b6e40fcf252c88f1a'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroKValue':'c79c0fa12bf371f4d75051755faf52c6dd3e49adf0411bf5ae836eadee21d7ac','Sign33MacroDependentA0':'2cbf54691d0430b46e6485ed18a3cbd542645537efb69bc4001d990f66b32f05',names[0]:objs[0],names[1]:objs[1]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150,100][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 for th in ([['path22_27','path23_27'],[],['path36_41']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointA0.{th}' does not depend on any axioms" in log
 for th in ([['lookup22_27','lookup23_27'],['d35_P_value','d35_K_value','d36_A0_value'],['lookup36_41','d41_A0_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointA0.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint36-41-a0-prelaunch-frontier-independent/check.py';assert H(pre)=='26d7d82b0a943af6653ff2556fa7ec42ce6566fdfb63c83092a69ed69fe93b31';up=D/'reviews/nine-seed33-jones-checkpoint22-23-pk-terminal-frontier-independent/check.py';assert H(up)=='7750fb217a5ab3eb62c56d17dbe0fec634126909a63f79103b4455676c85c862';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':4154,'stages':3,'guards':350,'links':1152,'scope':'A0 d36/d41 and P/K paths only; no full output semantics'},sort_keys=True,indent=2))
