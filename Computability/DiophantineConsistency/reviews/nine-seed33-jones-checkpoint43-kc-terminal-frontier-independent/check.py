#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint43-kc-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint43-kc-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='68e53e87ace2eb61aab274fb7d02b1cf3eca8d89ae3be770e09d9986a8aa16dd' and H(A/'outer-terminal-author-record.json')=='ec075fcc96db1a0fdf80e3093c448357c29ed60b16bf3329e3cc1cb6b454b90a';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(86112,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1164 and s['runner_sha256']==H(P/'run.py')=='1a157eacd26af74882f9c878aa57d750104bf984744c90c62655738d096db60b';r=s['rows'][0];n='Sign33MacroKcValue';assert r['module']==n and r['source_sha256']=='b7523dbdc0ecd67d8693e2aed865f2fe32c219666a7ec139eca250924893b840'==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']=='b5a5ca999049d1bb33c78707ca1df53cc9a1929837fa6922ffc8af31d518a2a9'==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
for phase in ('deps','compile'):
 v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
v=r['dependencies']['DiophantineConsistency.Sign33MacroDmValue'];assert v['sha256']=='c4245be96e4dd398e59037d7c92aef8e2f07e5063313ecfc9ef9e8e40bdbbe02' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
for th in ('d42_Bd_value','d43_Kc_value'):assert f"'DiophantineConsistency.Sign33MacroCheckpointKc.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint43-kc-prelaunch-frontier-independent/check.py';assert H(pre)=='66fdfcc57fa5cbc18bedbedf2ee4b9e0155377d327a46c0e1a2573a3c8fee035';up=D/'reviews/nine-seed33-jones-checkpoint42-dm-terminal-frontier-independent/check.py';assert H(up)=='cefa8b945e4458f17de3124d0703c9fe7bac7db2eeb5c5604cdcccbfbc6d6153';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':86112,'guards':100,'links':1164,'scope':'d42 Bd carry and symbolic Kc d43 only; no full output semantics'},sort_keys=True,indent=2))
