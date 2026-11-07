#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-u-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-u-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'38684d452247c485eea2dade759bc7563f7ac85f04b7e9e0ec0c4b584a3d0b63','Sign33ForwardNormU-compile.txt':'a2ff7c90ea11b088e209e797a2f3fea4a7ae9e6f8677a78a3bba31f32918b2ab','outer-observation.json':'541c20b1d771a4234227341b12bcd89fb0ed930493bc10cd082e417b66afd1e7'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(52489,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33ForwardNormU38','Sign33ForwardNormU'];objects=['c0194b4c89089d6ef9c300e36ba8bb2c4ed6c462e499f17d6819d2b9d4f86fde','916bdc378cbef5d02a3382b27bf0f028deeb75690fe85bf0145b548e4dda6608']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='u_terminal' if i==0 else 'norm_u_of_core';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd','Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'} if i==0 else {'Sign33ForwardNormU38':objects[0],'Sign33Node78Factor':'6fdc177f8aece228d1c1f44d0cb75403a69e864342536ec25128d9ce9819ec18','Sign33NegativeNode76':'dcea09d50e442b764ad418e791efb584b34790dd5fbaef6bc20a475cee958d8b','Sign33AbstractProjection32':'75605a5bc4bd7be7e03df76302b8a242b1f4244c02820b37b25650dbd8aa7bbc','Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==(250 if i==0 else 300)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==1 and (a/'Sign33ForwardNormU-compile.txt').read_text().count('warning:')==1 and len(s['overlay_links'])==1202
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':52489,'stages':2,'reports':2,'warnings':1,'direct_guard_slots':550,'overlay_links':1202,'scope':'conditional forward U field; no Lean replay'},indent=2,sort_keys=True))
