#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint38-39-v-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint38-39-v-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='6475a5d497ea1e75f8d50c9acc3299cdc8ad7606bc18d3b7de453885a0a7597e' and H(A/'outer-terminal-author-record.json')=='5ccddcac937473ab9f97593dfbf2a50b671cfdf3693b6828b560bce8e8f6ff34';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(92957,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1157 and s['runner_sha256']==H(P/'run.py')=='81c81209fefd1bad01a1f49f5e870ed3620acecca10b36ad1b04e7eb9be0c65b';names=['Sign33MacroV0Value','Sign33MacroV1Value'];objs=['c51424724e11b4e6eab31c7efa4bd021f9776f45cd9e5bf159c20c0f1d272161','e46eb589fdd00385f74916f8328d763280b54b5222d2bad44871385fca92a817'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroA1Path':'98f11ebc06ba14f40b1e5a6b2f268fdcf752453ef3c88c15062c62c0c469495e','Sign33MacroDependentV':'f42c741c3a2206f367c1c7d69b92af2a726d5520d64eae06ddb31dcebe08f789',names[0]:objs[0]}
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
 for th in ([['d38_V0_value'],['d39_V1_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointV.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint38-39-v-prelaunch-frontier-independent/check.py';assert H(pre)=='8968a05b82077923a786ca88c3e083bcaff3640adde9fa154f80eb99ff090e31';up=D/'reviews/nine-seed33-jones-checkpoint37-41-a1-terminal-frontier-independent/check.py';assert H(up)=='6f7ddff2156a7e4d937d4228c0f4a333fb0659d5f929fbee2d49878e3353f7dd';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':92957,'stages':2,'guards':300,'links':1157,'scope':'V0 d38 and V1 d39 symbolic values only; no full output semantics'},sort_keys=True,indent=2))
