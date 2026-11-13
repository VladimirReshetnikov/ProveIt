#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent01-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent01-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='050e6fdcfe81d6d70745e376f046c0d7ffecb94a50a2bf44449dcca7f6cc73c2' and sha(A/'outer-terminal-author-record.json')=='79fa09681ad0cd332085ac30121b3b666f09c06428bc1505ae970e07eb864ba5';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(20305,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1086 and s['runner_sha256']==sha(P/'run.py')=='da7d4b187816c559f5fd65e2a7fb01ef10d9b16a9d05673ee3079edb90945b71';names=['Sign33MacroDependentU','Sign33MacroDependentY'];objects=['c27a117b5552898cd6475a1f8823bc5aa6d669fac32775c919c96453c98a88a4','14f9815d4dbf41a173a275175da5a02ac7b602c610135d0cbf1ba1ce2cb6ea8e'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['prefix_U'],['prefix_Y']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroLive18Group01','9ad348b1432ec9acb52c84a5605cf91131d04c1c4b7f8470715298eb582d99d1') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent01.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent01-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='0f8feb266992fd8fe6246412b3582b4f021c0aa300e84559272be358033acf2d'
up=D/'reviews/nine-seed33-jones-live18-staged-terminal-frontier-independent/check.py';assert sha(up)=='3e8a840b8e3b9450e1b3b700e809444fea30795b62f75bbca53fbbd1daf685c0';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':20305,'stages':2,'guard_slots':200,'overlay_links':1086,'scope':'local d19 U and d20 Y prefix equations only; no output equality'},indent=2,sort_keys=True))
