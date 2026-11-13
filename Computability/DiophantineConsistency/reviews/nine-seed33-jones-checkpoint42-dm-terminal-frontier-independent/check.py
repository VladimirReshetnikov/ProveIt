#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint42-dm-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint42-dm-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='f044ee14dc75462ae07697c8b26014da12838baca4c8fbe4a0fdacac37a148e5' and H(A/'outer-terminal-author-record.json')=='81c9c65a5bfb85152c47c318f915d5dcf012ba39a2230be56ab61a846b8f6c5a';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(90901,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1162 and s['runner_sha256']==H(P/'run.py')=='5c250d60f2f68f18bea2bdb45f4d1adf8d518aeb42c0665f00d13ed9d48dc827';names=['Sign33MacroDmInputs','Sign33MacroDmValue'];objs=['4d88411dac727e18487ec5af6ddd585c42b993a51578b50c381af8e3deea084f','c4245be96e4dd398e59037d7c92aef8e2f07e5063313ecfc9ef9e8e40bdbbe02'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroCdValue':'9e333cf5e24bae7952bc4c9c7c6a81c7d444ebe83f3c4819e92d0e3e78e94cf4','Sign33MacroCheckpoint41to45':'71ed9dcb4bef7528b777f26b3f787c6ca0e6d93ab7b14f15f2841b82ba300fd6','Sign33MacroDependentDmKc':'405792555e97d6dff1e6f1a2c9b309d14b17b97b00d4df2a0a806fe21815f7d4',names[0]:objs[0]}
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
 for th in ([['d41_K_value','d41_Y_value'],['d42_Dm_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointDm.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint42-dm-prelaunch-frontier-independent/check.py';assert H(pre)=='0a9b0a22db543f72d6111646e672bcce04d396c83c16de778a58c9b4a88767da';up=D/'reviews/nine-seed33-jones-checkpoint40-41-bdcd-terminal-frontier-independent/check.py';assert H(up)=='a3caeb4ec40667b1924730943938ef08bc5222282a24c24136dd945df44d8bfb';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':90901,'stages':2,'guards':300,'links':1162,'scope':'d41 K/Y and symbolic Dm d42 only; no full output semantics'},sort_keys=True,indent=2))
