#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-abstract-projections28-32-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-abstract-projections28-32-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'db2eaf9f695f596451f3cefa87f5051b4c2bf56d32c7e43d3c8279c79b0e5932','Sign33AbstractProjection32-compile.txt':'1de073871c2f6e98cf31c9fdba5ba15b56e938d1ca0e4251df48ca601b0b8918','outer-observation.json':'74654bb947c4910e72cd01d37630ef58882203da6445b1d78b5109dd2be1f98e'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['exit_code'])==(80913,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33AbstractProjection28','Sign33AbstractProjection32'];objects=['1532f0e6bda81a064eb6dce32946cc17efcc00637d5a4758e5c446740a7173e3','75605a5bc4bd7be7e03df76302b8a242b1f4244c02820b37b25650dbd8aa7bbc']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='project';assert all(re.search(r"'DiophantineConsistency\."+n+r'\.'+t+r"' depends on axioms: \[propext\]",log) for t in ('template','project'))
 expected={'Sign33AbstractTuple':'fa8ec17dc816676fcfa21edc6270fe24ba4231337653034b2d033ff5d60c5373'}
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33AbstractProjection32-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1196
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':80913,'stages':2,'reports':4,'warnings':0,'direct_guard_slots':200,'overlay_links':1196,'scope':'abstract and concrete coordinate28 and 32 projections; no Lean replay'},indent=2,sort_keys=True))
