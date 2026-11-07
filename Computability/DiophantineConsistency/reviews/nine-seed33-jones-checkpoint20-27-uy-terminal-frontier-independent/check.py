#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint20-27-uy-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint20-27-uy-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='6f45e8aa3bb2a0740a740bf129ae869d35e15d49be109219bb65f3654716d1a0' and H(A/'outer-terminal-author-record.json')=='4d3aa5cca80f628d96ee18a432c60e428f82aac1c3de029813c63eafbeb35443';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(36942,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1124 and s['runner_sha256']==H(P/'run.py')=='41cd5e6e1fad7b7dfadc3f5877cd905a9169717894a670b5e920a72aa10b401d';names=['Sign33MacroUYInputs','Sign33MacroUYPath','Sign33MacroUYValues'];objs=['79f57b67d14168984ec8f210f813c42a8e81c105fc038fd747df05dfc97b67c8','2ad8caf78de55646bc606f070080aa40e4c02c073216d994866f98aca8dd5a9f','1ff9ee127bf870a715bc52aab178c8fece58dfceafd6700783d4830519aa67c6'];ths=[['d18_N_value','d18_s_value','d18_w_value'],['lookup20_27'],['d27_U_value','d27_Y_value']];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroCheckpoint41to45':'71ed9dcb4bef7528b777f26b3f787c6ca0e6d93ab7b14f15f2841b82ba300fd6','Sign33MacroLive18Group01':'9ad348b1432ec9acb52c84a5605cf91131d04c1c4b7f8470715298eb582d99d1','Sign33MacroLive18Group03':'3fb6663a5d3070e902df9e95f4accd0058a7ada288923837f0c1464273388364','Sign33MacroPrefixInputsA':'3cfc3529c97019bfa57f20d136eef22d4e822771b6cf2da051b5a6d9e61eacab','Sign33MacroPrefixQNCarry':'c35a2307d35050bac27cb469bb3acf21ecca0d94c925eb440b981eb8b258b50b','Sign33MacroDependentY':'14f9815d4dbf41a173a275175da5a02ac7b602c610135d0cbf1ba1ce2cb6ea8e',**dict(zip(names,objs))}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[300,100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointUY.path20_27' does not depend on any axioms" in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroCheckpointUY.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint20-27-uy-prelaunch-frontier-independent/check.py';assert H(pre)=='5a038ae3576c4cd21529fd78fc47181d8d46e82e6ddad93ab8cf408a43b51419';up=D/'reviews/nine-seed33-jones-checkpoints27-45-staged-terminal-frontier-independent/check.py';assert H(up)=='2d33d03b58de071f6c0a2b28afe041d708e07a1c1e850632cabe3e13fce92a66';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':36942,'stages':3,'guards':550,'links':1124,'scope':'d27 symbolic U/Y and d20→d27 lookup only; no full output semantics'},sort_keys=True,indent=2))
