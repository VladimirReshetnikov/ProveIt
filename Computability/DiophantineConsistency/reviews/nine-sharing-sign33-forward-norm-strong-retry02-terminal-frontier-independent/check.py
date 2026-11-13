#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-strong-retry02';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-strong-retry02-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'8ff5f481078daae9259ee3f9f7180e8c567a1d8c76c7fd5ef0d1e379e773a5ad','Sign33ForwardNormStrong-compile.txt':'009a6b0261a66915fda2a6fba6d04dc472aa57cabc14b1798f998f3a906bc963','outer-observation.json':'7291f4b216fb704276929c6c702bfaf35a803243c6acb28419cba654907760ec'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(96273,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33ForwardNormStrong38','Sign33ForwardNormStrong'];objects=['396c5de6c405053ee4d923b7f2391ae37f83cd9c10e054f689a7c17a9eb9465b','c6adcef3865edd72fca6880f2cc7974913f1595da0b1246cc736e00cf11fdbcc']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='strong_terminal' if i==0 else 'norm_strong_of_core';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd','Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'} if i==0 else {'Sign33ForwardNormStrong38':objects[0],'Sign33AbstractProjection22':'5d393ae2cd442db4b3d20fe3fcb2b99abda6988fa493c3151092ffa2aeb890a8','Sign33AbstractProjection28':'1532f0e6bda81a064eb6dce32946cc17efcc00637d5a4758e5c446740a7173e3','Sign33AbstractProjection32':'75605a5bc4bd7be7e03df76302b8a242b1f4244c02820b37b25650dbd8aa7bbc'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==250
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==1 and (a/'Sign33ForwardNormStrong-compile.txt').read_text().count('warning:')==1 and len(s['overlay_links'])==1198
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':96273,'stages':2,'reports':2,'warnings':1,'direct_guard_slots':500,'overlay_links':1198,'scope':'conditional forward strong field; no Lean replay'},indent=2,sort_keys=True))
