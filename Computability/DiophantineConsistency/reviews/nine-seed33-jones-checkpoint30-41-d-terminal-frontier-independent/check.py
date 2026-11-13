#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-checkpoint30-41-d-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-checkpoint30-41-d-check-20261106');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(A/'state.json')=='fb0e0fe95def995d1b76707a2152334715f6da2da29981f79f8a0690d0f45401' and H(A/'outer-terminal-author-record.json')=='170542e6ef9cef8335dd0131fc2e719772845a6afadb14b9d59f3061ba225ba8';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(14356,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1138 and s['runner_sha256']==H(P/'run.py')=='aeedfdc389465190d0ada74cd885af0ed2ab0609c5a9985dfebd7fb83991cfb5';names=['Sign33MacroDValue','Sign33MacroDPath'];objs=['58a02e82bb9bcfb1f95871ba5ed864d7230af53a46592d4c28cfc472bfb099df','6fd0f837045b66a69f7b6c5b00b643c6295ec9b81f1f10e18b9118739e51b2ac'];m=json.loads((P/'source-manifest.json').read_text())['rows'];pins={'Sign33MacroAValue':'7fbf4ea8332abaca614384a975c891dba2553b4205e28654798898f426852f51','Sign33MacroDependentD':'543e77ef6f0755c67375c1fe4e7be11d8e846a8c150177de7ecde1e3ad73a9a0','Sign33MacroQPath':'fd2e415af7be3edd855e46ea16a0763975a7b57f32d8f058861992c7dfe6771c','Sign33MacroCheckpoint34to41':'593e6f35fe1fdfe2975416231b071c118275581007ffe71b72323f19aaeffa5d',names[0]:objs[0]}
for i,(r,n,obj,e) in enumerate(zip(s['rows'],names,objs,m)):
 assert r['module']==n and r['source_sha256']==e['source_sha256']==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==H(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==[200,150][i]
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert H(A/f'{n}-{phase}.txt')==H(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256']
 for mod in e['imports']:
  v=r['dependencies'][mod];assert v['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
 log=' '.join((A/f'{n}-compile.txt').read_text().split());assert 'warning:' not in log and 'sorryAx' not in log and 'error:' not in log
 if i==1:assert "'DiophantineConsistency.Sign33MacroCheckpointD.path30_34' does not depend on any axioms" in log
 for th in ([['d29_A_from_d27','d30_D_value'],['lookup30_34','d41_D_value']][i]):assert f"'DiophantineConsistency.Sign33MacroCheckpointD.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
pre=D/'reviews/nine-seed33-jones-checkpoint30-41-d-prelaunch-frontier-independent/check.py';assert H(pre)=='97e96696372d3d1ea8a089eff5c126eedc05e0329c36accbd527dde221792f60';up=D/'reviews/nine-seed33-jones-checkpoint29-41-q-terminal-frontier-independent/check.py';assert H(up)=='a8c8746ca9abb84c0d9d0f18f6db85145d862a68be849793a19cd9ce1dabe15f';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':14356,'stages':2,'guards':350,'links':1138,'scope':'D values d30/d41 and d30→d34 lookup only; no full output semantics'},sort_keys=True,indent=2))
