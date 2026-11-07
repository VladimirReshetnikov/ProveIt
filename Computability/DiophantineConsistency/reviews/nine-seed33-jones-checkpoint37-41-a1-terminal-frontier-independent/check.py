#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint37-41-a1-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint37-41-a1-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='32aabd5f01d75fbfc86a7db8ee2fdbf3d10e3d2e587505b2cbc5e35783c2d681' and H(A/'outer-terminal-author-record.json')=='12e1559a11677d9f152c3e2a94d2204e27aaff9d30e22bfad2298893ca5af270';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(30701,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1155 and s['runner_sha256']==H(P/'run.py')=='fe9e43d862de849c377e446f5eaef425adf01052445030a3d777b3b50e46c208';names=['Sign33MacroA1Value','Sign33MacroA1Path'];objs=['c09eb10e2bd203e5b5504e455954a3c8c3a5674fce758d95bbc9e8874187ca4d','98f11ebc06ba14f40b1e5a6b2f268fdcf752453ef3c88c15062c62c0c469495e'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroA0Path':'8e746bd55046055067b7dad1e5f10ff22063c186b7ed4e2b6e40fcf252c88f1a','Sign33MacroDependentA1':'bec5da4c4f0e4aa767ffe019ba460e3e5f64645db1de0b1f408c78e5940091c7',names[0]:objs[0]}
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
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointA1.path37_41' does not depend on any axioms" in log
 for th in ([['d37_A1_value'],['lookup37_41','d41_A1_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointA1.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint37-41-a1-prelaunch-frontier-independent/check.py';assert H(pre)=='e9c4d15f3f3e59a37705b1f0fc74cbd19fc8845a188d15309cb12a5a5ee7b839';up=D/'reviews/nine-seed33-jones-checkpoint36-41-a0-terminal-frontier-independent/check.py';assert H(up)=='9130ac2985209a82b48723044ce7f5529646212cd28c10738f55442d7228e6d7';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':30701,'stages':2,'guards':250,'links':1155,'scope':'A1 values d37/d41 and d37→d41 path only; no full output semantics'},sort_keys=True,indent=2))
