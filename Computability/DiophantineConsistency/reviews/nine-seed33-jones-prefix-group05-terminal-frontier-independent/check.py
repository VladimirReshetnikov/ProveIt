#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-prefix-group05-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-prefix-group05-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='f1248d358bf47604cc73a226a6e045379a36cd2c13bcca7ac8bb96d0ffcbb12d' and sha(A/'outer-terminal-author-record.json')=='ae6432a526e162d820e2790675719e0a99d41b09bfa6d5b610ecf76e598d55b0';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(59753,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and len(s['overlay_links'])==1071 and s['runner_sha256']==sha(P/'run.py')=='9cee097cfc4eaa76d93526e08ee3a5ae48e6e64ab8a9d5329d80188039e2180f';names=['Sign33MacroPrefixQNCarry'];objects=['c35a2307d35050bac27cb469bb3acf21ecca0d94c925eb440b981eb8b258b50b'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d10_q','d10_N']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroPrefixGlarge','1887baa3203c288e248f8ee85eb0af794de72272dbde1c039a8774ebc4735e2f');v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroPrefixGroup05.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-prefix-group05-prelaunch-frontier-independent/check.py';assert sha(review)=='3bdf5ebae13c26675a668772035f2d9421873fbb2a3eec6910fbc148c8220c0f'
up=D/'reviews/nine-seed33-jones-prefix-group03-staged-terminal-frontier-independent/check.py';assert sha(up)=='ab4237754322f7aa5c7c769ce0068235e656272fc30a2f7e7910ab2559de8c22';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':59753,'stages':1,'guard_slots':100,'overlay_links':1071,'scope':'symbolic q/N d10 short prefixes only; no output equality'},indent=2,sort_keys=True))
