#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-abstract-projection22-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-abstract-projection22-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'2464c7f1a7f03d85770c354c5dbb5130c51edf6fdce392e297732373b0cdb8eb','Sign33AbstractProjection22-compile.txt':'bb303af2019988b1fe47ec5aefb82704646addfa571c58688ccd9fd85beb7acf','outer-observation.json':'b1beb9d90a73e45815156128d5dd5ef6c340bc629c384b4403fcc4b65f4edfbb'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(51210,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33AbstractTuple','Sign33AbstractProjection22'];objects=['fa8ec17dc816676fcfa21edc6270fe24ba4231337653034b2d033ff5d60c5373','5d393ae2cd442db4b3d20fe3fcb2b99abda6988fa493c3151092ffa2aeb890a8']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='project22' if i==0 else 'project';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext\]",log)
 expected=({'SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b'} if i==0 else {'Sign33AbstractTuple':objects[0]})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33AbstractProjection22-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1194
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':51210,'stages':2,'reports':2,'warnings':0,'direct_guard_slots':200,'overlay_links':1194,'scope':'abstract and concrete coordinate22 projections; no Lean replay'},indent=2,sort_keys=True))
