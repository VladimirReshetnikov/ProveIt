#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent04-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent04-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='48eb2457d081e0ff4a2cf94c84a016603d28f9f8bfea606ff252519d23561a81' and sha(A/'outer-terminal-author-record.json')=='6baf03454b94ba308a8331c8ad2fe8e56190a6917b4cfba89cc99436f9df02d8';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(27673,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and len(s['overlay_links'])==1095 and s['runner_sha256']==sha(P/'run.py')=='27ea0e8a16895c4a19f73106be380c7a5071d9060a757cb233d12cf234154bd7';names=['Sign33MacroDependentJ','Sign33MacroDependentQ','Sign33MacroDependentD'];objects=['2e13b7fec88baed73ca02e1507eae18bb762990dc852e9619d02545b83abe272','855c7e0cb6a6ec478e701e9b3c9369b85f84b3d6126cbdfb19aafee4c92f2572','543e77ef6f0755c67375c1fe4e7be11d8e846a8c150177de7ecde1e3ad73a9a0'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d27_A_carry','prefix_J'],['d28_W_carry','d28_C_carry','prefix_Q'],['d29_A_carry','d29_C_carry','prefix_D']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentC','7d4b8010fa88f6b17f163b5e897ca76484416a2ee4c82d1e1b371f78ba6eb389') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent04.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent04-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='c528edee2aebdc7a9c1e63e2aad2cc3a7e52dcb1694a7cd59060aa4210b55a5d'
up=D/'reviews/nine-seed33-jones-dependent03-staged-terminal-frontier-independent/check.py';assert sha(up)=='ffe09bb2427381c09cb02c664975f0f0a95e99d058c92be92b6c4dd70ce7baa6';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':27673,'stages':3,'guard_slots':300,'overlay_links':1095,'scope':'local d28–d30 J/Q/D prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
