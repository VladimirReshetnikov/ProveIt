#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-seed-iff-check';A=P/'attempt01';O=Path('/tmp/nine-sharing-sign28-seed-iff-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='b6a4477fecc1a2629f856ab0ad7891a93a4fff0bcf6c7ab382c81fb917a55bd2' and sha(A/'outer-result.json')=='da352cbc00eabb6481a46f0e5bfabde199c0bb0fc49aac05cfde4f0f9713c08d';o=json.loads((A/'outer-result.json').read_text());assert (o['author_observed_outer_session'],o['author_observed_numeric_outer_exit'])==(30087,0) and o['retained_state_sha256']==sha(A/'state.json')
s=json.loads((A/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and len(s['overlay_links'])==1070 and s['runner_sha256']==sha(P/'run.py')=='6bd046249d5c548494561f9fe9bd8ebf8ccd7ec521b8ebb3536fdd2c1de129c8';names=['Sign28SeedPointwise','Sign28SeedExistential'];objects=['2d89fe81188ae72dfa035b8f70f7d14435a275202fcaedcd0c8d7b49e5d9abc0','f8b2788e3395c755ce1efa95773af9c3e8d564d01a21fd45bb52a7610ecdcbe4'];m=json.loads((P/'source-manifest.json').read_text())['rows']
for i,(r,n,obj,entry) in enumerate(zip(s['rows'],names,objects,m)):
 assert r['module']==n and r['source_sha256']==entry['source_sha256']==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and r['object_sha256']==obj==sha(O/'lib/DiophantineConsistency'/f'{n}.olean') and len(r['direct_guard'])==100
 for phase in ('deps','compile'):
  v=r[phase];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==o['logs'][f'{n}-{phase}.txt']==v['log_sha256']
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 mod,h=('Sign28ReverseBridge','5f7ce280d06fc119b5edd7256a309ab8e0291a4689e4c516a28d185b96442f01') if i==0 else (names[i-1],objects[i-1]);v=r['dependencies']['DiophantineConsistency.'+mod];assert v['sha256']==h and r['direct_guard'][v['path']]=={'sha256':h,'realpath':v['realpath']}
 log=(A/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'sorryAx' not in log
 for th in ([(f'Sign28SeedIff.{x}','[propext, Classical.choice, Quot.sound]') for x in ('drop_lift','pointwise')],[('Sign28SeedIff.exists_same_input','[propext, Classical.choice, Quot.sound]')])[i]:assert f"'DiophantineConsistency.{th[0]}' depends on axioms: {th[1]}" in ' '.join(log.split())
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
review=D/'reviews/nine-sharing-sign28-seed-iff-prelaunch-frontier-independent/check.py';assert sha(review)=='c3398c25b6afe5a4bf785f301a3cc0fadff19022933e9ea88dccaed0984cbc43'
review=D/'reviews/nine-sharing-sign28-zero-bridge-terminal-frontier-independent/check.py';assert sha(review)=='5e05f8aee82844d520d04905f9f27ee72bc9a66dd5b6bb0637b57e2d30a8c17d';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,capture_output=True,timeout=30)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':30087,'stages':2,'guard_slots':200,'overlay_links':1070,'scope':'same symbolic ports and beta cast; sign28 pointwise and same-input existential iff sign31 in IΣ₁; no source/iPRA composition or JSON/degree binding'},indent=2,sort_keys=True))
