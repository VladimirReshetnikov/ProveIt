#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint24-27-a-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint24-27-a-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='8f57f0ee28ce62d6804bb7a1b1d12a77356219e083da4cb9ca0e1d5e048e216f' and H(A/'outer-terminal-author-record.json')=='47b2f3bfcde2851e167691c7b40e5fc5e426a80e1e7b8e39cb51fab30899806a';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(72692,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1129 and s['runner_sha256']==H(P/'run.py')=='78592a7af12911d4247a1116a22944091cd681955eeeafd7f21548cd18a580de';names=['Sign33MacroAPath','Sign33MacroAValue'];objs=['0760766bfee1db44e61309e67a49aa06e48e3bc627fab7268b900afd52ad1353','7fbf4ea8332abaca614384a975c891dba2553b4205e28654798898f426852f51'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroMValue':'ae5f60f5efd022e5372faffbfc61d5033ac0afe86da416c069cfdb1c2d74beb2','Sign33MacroDependentA':'c03e76f45713f3b8ab33c64f4699ab10196a9b2b7fa7d2f58bec4e4a495eec3e',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[100,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==0:assert "'DiophantineConsistency.Sign33MacroCheckpointA.path24_27' does not depend on any axioms" in log
 for th in ([['lookup24_27'],['d27_A_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointA.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint24-27-a-prelaunch-frontier-independent/check.py';assert H(pre)=='7a10759ce96e3a67f77c043449a194f492858ac13f44f1e7c8cb38b14a7f5f4e';up=D/'reviews/nine-seed33-jones-checkpoint21-27-m-terminal-frontier-independent/check.py';assert H(up)=='e5c0fa27c0ddf5604f2174210b5a37263327260ea1f85afbf014a9bc7c74b1ef';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':72692,'stages':2,'guards':250,'links':1129,'scope':'d27 A with opaque d11 rank, d24→d27 lookup only; no full output semantics'},sort_keys=True,indent=2))
