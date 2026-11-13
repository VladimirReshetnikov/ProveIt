#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-dependent03-staged-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-dependent03-staged-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='ef9d587daff77a6926fec547e6ca4755244824a3a3230e41dc987493882b6a2e' and sha(A/'outer-terminal-author-record.json')=='dbc1a034967b8a6eb64570cdcca744d1daaa0f829b4a49cef9a58b96d774084e';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(7888,0)
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4 and len(s['overlay_links'])==1091 and s['runner_sha256']==sha(P/'run.py')=='92b3c11acea4ed6cb2c2436b866a7f953fcf2e79b8f2493f7eab75cf2c86de29';names=['Sign33MacroDependentA','Sign33MacroDependentBprime','Sign33MacroDependentW','Sign33MacroDependentC'];objects=['c03e76f45713f3b8ab33c64f4699ab10196a9b2b7fa7d2f58bec4e4a495eec3e','ea70bf1cebe2e90a99147b66bfe3e4a72923909edf15569fedcc97d8db2896c8','923a2e06a49e01c89605bc01f9c59dedc5138cc92adf90a5a12cb7838b062f57','7d4b8010fa88f6b17f163b5e897ca76484416a2ee4c82d1e1b371f78ba6eb389'];m=json.loads((P/'source-manifest.json').read_text())['rows'];ths=[['d23_M_carry','d23_U_carry','prefix_A'],['d24_R_carry','prefix_Bprime'],['d25_b_carry','d25_w_carry','prefix_W'],['d26_phi_carry','prefix_C']]
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign33MacroDependentK','d8702218c9633485b986a49cb9cb4308027648156649c3babd196f612f751174') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ths[i]:assert f"'DiophantineConsistency.Sign33MacroDependent03.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-seed33-jones-dependent03-staged-prelaunch-frontier-independent/check.py';assert sha(review)=='32e4426b513a6ebffc7509976f71d3e8306001a885463f73f0445d61b91c87f2'
up=D/'reviews/nine-seed33-jones-dependent02-staged-terminal-frontier-independent/check.py';assert sha(up)=='c663a5ba9ee0a038349f035833770b9c64db8e7e14a4b43c548a3370720f2141';subprocess.run([sys.executable,'-I','-S','-B',str(up)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':7888,'stages':4,'guard_slots':400,'overlay_links':1091,'scope':'local d24–d27 A/Bprime/W/C prefix equations and carries only; no output equality'},indent=2,sort_keys=True))
