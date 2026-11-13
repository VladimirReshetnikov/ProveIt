#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint29-41-q-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint29-41-q-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='fc7d5ab2edad0c7fe411077bd7179cd45b22916d2b6df114f71c7c4de02da784' and H(A/'outer-terminal-author-record.json')=='f01cef7a0c5665e49d7176e7baca861726eaf84f249d372034321f8366a43f67';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(77713,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1136 and s['runner_sha256']==H(P/'run.py')=='ceee06de03cbf50e818009b19916cb1467406c362f17edfb7a5142c9400cbe81';names=['Sign33MacroQValue','Sign33MacroQPath'];objs=['66798ce4e8bccbf9713034befb023db713b721ee5b75c32e4ee902a6957d71c5','fd2e415af7be3edd855e46ea16a0763975a7b57f32d8f058861992c7dfe6771c'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroCValue':'4adbe317020d9cee22d6e735562baa3cd21e0319067c98e66f403dcbfc0d9f2b','Sign33MacroDependentQ':'855c7e0cb6a6ec478e701e9b3c9369b85f84b3d6126cbdfb19aafee4c92f2572','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
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
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointQ.path29_34' does not depend on any axioms" in log
 for th in ([['d29_Q_value'],['lookup29_34','d41_Q_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointQ.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint29-41-q-prelaunch-frontier-independent/check.py';assert H(pre)=='aecf5e1ebc5e81efe3af71b1ccb492cbb1ab464a97beed89725f9ebffe1692ff';up=D/'reviews/nine-seed33-jones-checkpoint26-27-c-terminal-frontier-independent/check.py';assert H(up)=='7a3f2f1374387246c434d048cb451dc999664387ee830048728a696b768097be';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':77713,'stages':2,'guards':300,'links':1136,'scope':'Q values d29/d41 and d29→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
