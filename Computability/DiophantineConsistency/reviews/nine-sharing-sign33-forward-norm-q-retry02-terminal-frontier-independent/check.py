#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-q-retry02';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-q-retry02-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'39dde1f529c3b65a07bfa40dd21a003711d673d1191df4e75b8945261533a26f','Sign33ForwardNormQRetry-compile.txt':'a9341fcf3a9671c770c5b2c127f0a70c7e642d73f3d2fe5c929d04f5287b6449','outer-observation.json':'99a4df313fc4bb66c59855b4888a7deb55e8e507948447086e81d46525e77a4e'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(65628,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33ForwardNormQ38','Sign33ForwardNormQRetry'];objects=['f5d4af8af1c9025e555f7f8b3611cf0dce33fce60f1331ce2779ae6922441dbe','63cb5c455231c7536b955abe4485243d0bcfd111c89bd6862fae3de91470d24f']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='q_terminal' if i==0 else 'norm_q_of_core';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd','Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'} if i==0 else {'SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','Sign33ForwardNormQ38':objects[0]})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(250 if i==0 else 150)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==1 and (a/'Sign33ForwardNormQRetry-compile.txt').read_text().count('warning:')==1 and len(s['overlay_links'])==1194
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':65628,'stages':2,'reports':2,'warnings':1,'direct_guard_slots':400,'overlay_links':1194,'scope':'conditional forward Q field; no Lean replay'},indent=2,sort_keys=True))
