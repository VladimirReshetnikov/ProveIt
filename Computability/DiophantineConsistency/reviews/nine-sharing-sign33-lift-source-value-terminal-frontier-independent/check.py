#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-lift-source-value-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-lift-source-value-check-20261106');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'state.json':'9644484ac86d0e3a7a260c2df113c28edab5fe9d983a22310b7844e899585139','Sign33LiftSourceValue-compile.txt':'6690d12c0326704394f7183c232f4234ec5ddce983303e94b977048c38330441','outer-observation.json':'7576d6bea02e092c5931c6b7dcef4285af519e6ece4d62cfdc3ddb38d42b64d1'}.items():assert sha(a/n)==h
outer=json.loads((a/'outer-observation.json').read_text());assert (outer['session_id'],outer['numeric_exit'])==(93721,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Sign33LiftTerminals','Sign33LiftSourceValue'];objects=['37acff3d93e699632a8fd763bd9df1afd5c0acb7f7d673c6ba146c689eb1a6a0','272162da4a79b3ab25ac86242ef160ae137447dee9ad0313a6fd2bc845f10acb']
warning_count=0
for i,(r,n,h) in enumerate(zip(s['rows'],names,objects)):
 assert r['module']==n and r['object_sha256']==h and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==h and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for phase in ('deps','compile'):
  x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'error:' not in log and 'sorryAx' not in log;warning_count+=log.count('warning:');theorem='terminals' if i==0 else 'allcuts_imply_value';assert re.search(r"'DiophantineConsistency\."+n+r'\.'+theorem+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 expected=({'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Sign33RingGatesAssembly':'f2a70591bb828df70f3b1a70bc93a927ed77e3f406af39577ec56aefa81e0d09','Sign33RingTopology':'12541ed2f43c8fa4e2bee94b089ef7f74802fe15cf253809b6e659bde73365b5'} if i==0 else {'Norm38StaticCarrierConditional':'7d0b8cbb7cd6a01447ff710deb1f22336c3765bc4e7b5149b9cc3424eef491f6','Sign33LiftFiveNorms':'5bd49f713cc65773f9d3c6cce99bcf68248a121b65f215bd895da26c0c7767b2','Sign33LiftTerminals':objects[0]})
 for mod,digest in expected.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'sha256':digest,'realpath':dep['realpath']}
 assert len(r['direct_guard'])==200
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert warning_count==0 and (a/'Sign33LiftSourceValue-compile.txt').read_text().count('warning:')==0 and len(s['overlay_links'])==1213
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':93721,'stages':2,'reports':2,'warnings':0,'direct_guard_slots':400,'overlay_links':1213,'scope':'AllCuts implies shifted Carrier65 ring value zero; no Lean replay'},indent=2,sort_keys=True))
