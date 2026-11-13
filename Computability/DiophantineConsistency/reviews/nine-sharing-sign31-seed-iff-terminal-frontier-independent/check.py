#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign31-seed-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='ae407f3085a083ee4eb4bff28e64a4cdcd698cac3b87bdb3a0163e231f86f511' and sha(A/'outer-result.json')=='83f8cf5058894bd13f47437782bdfdf7089656568738077dbc9208d2a675ac4c';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(58566,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1068 and s['runner_sha256']==sha(P/'run.py')=='ab07005e420055cba00e364ce0abe3b1c7c3231af4ac8c80b463b576111d39f5';names=['Sign31SeedPointwise','Sign31SeedExistential'];objects=['0e197fb297c922a45353833d296371bd5083fd30a9125785b71869357d285ed5','9f1e9a1537698844baa09d0461409f907e6d21b9396e5ab8ec35b4434fdafd64'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign31ReverseBridge','4ed14ddee585ff6b50922b908ca42e6a2205d965c090722e6d129e8e7d571603') if i==0 else (names[0],objects[0]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in (['drop_lift','pointwise'] if i==0 else ['exists_same_input']):assert f"'DiophantineConsistency.Sign31SeedIff.{th}' depends on axioms: [propext, Classical.choice, Quot.sound]" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign31-seed-iff-prelaunch-frontier-independent/check.py';assert sha(review)=='0e2bcc808f94354cdcb18c81e64edb71bd8dc96ec2b34c2cfb50dd69aa98792d';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':58566,'stages':2,'guard_slots':200,'overlay_links':1068,'scope':'same arbitrary input and symbolic ports, sign31/sign32 IΣ₁ equivalences; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
