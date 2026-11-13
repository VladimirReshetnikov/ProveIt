#!/usr/bin/env python3
"""Recheck retained two norm38 attempts; no Lean execution."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research'
first=R/'nine-sharing-norm38-check-sequence';retry=R/'nine-sharing-norm38-check-retry01'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(first/'attempt01/state.json')=='019e5f01533f7ceebdf9744fcce99a851cca878b78438dd3891610c6e360db87'
assert sha(retry/'attempt01/state.json')=='c50fef5f734b41dadf8455388486c5de86cbe979b2e65cbace72d0d91b95df89'
for packet,h,session in [(first,'29c4c6fd69b58838c3573bcaca5a13232c5a582bbd064fd2a870bca7e37782b5',48446),(retry,'d1f76bff9ac4273c14fc1b9fc38f83f9f1eaee57bec8ef3d92a28b4617054db7',16634)]:
 outer=packet/'attempt01/outer-terminal-author-record.json';assert sha(outer)==h
 v=json.loads(outer.read_text());assert v['outer_session_id']==session and v['outer_exit_code']==1 and v['runner_status']=='FAILED'
 assert 'not independently observed or a raw terminal transcript' in v['observation_kind']
assert sha(first/'run.py')=='3b54daf61b99632815a078a4d4fd6a5dba7b30181045b3e7b2eaf319761fe488'
assert sha(retry/'run.py')=='2dab121c54900c97abeed0072b96375f942f9e09b71872ea155db909c92b6fda'
f=first.joinpath('run.py').read_text();t=retry.joinpath('run.py').read_text()
assert f.replace('nine-sharing-norm38-sequence-20261105','nine-sharing-norm38-retry01-20261105').replace('860bc118705af6beb8c55f98036605506caa801460b058e4319791faa63304ac','932be1171be69ad79a6279b776af15788ee5f9e7a417397e04d94a0608af345d')==t
names=['SharingGateModel','ForwardWitness38','SharingSeed38','SharingNormTrace','SharingNormSquares','NormAssignment38']
for name in names:
 a=(first/'src/DiophantineConsistency'/(name+'.lean')).read_text();b=(retry/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 if name in ('SharingGateModel','SharingNormTrace'):
  assert a.count('Function.update_same')==(2 if name=='SharingGateModel' else 1)
  assert a.count('Function.update_noteq')==(2 if name=='SharingGateModel' else 1)
  assert a.replace('Function.update_same','Function.update_self').replace('Function.update_noteq','Function.update_apply')==b
 else:assert a==b
cache={}
def checkfile(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 key=str(p.resolve())
 if key not in cache:cache[key]=sha(p)
 assert cache[key]==h
def guards(g):
 for k,v in g.items():
  if v is None:assert not os.path.lexists(k),k
  else:checkfile(k,v['sha256'],v['realpath'])
snapshots=[]
for packet,out,expected in [(first,Path('/tmp/nine-sharing-norm38-sequence-20261105'),1),(retry,Path('/tmp/nine-sharing-norm38-retry01-20261105'),3)]:
 state=json.loads((packet/'attempt01/state.json').read_text());assert state['status']=='FAILED' and len(state['rows'])==expected
 assert sha(out/'state.json')==sha(packet/'attempt01/state.json')
 assert state['base_state_sha256']=='469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439'
 for k,v in state['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
 for row in state['rows']:
  n=row['module'];assert sha(packet/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
  for typ in ('deps','compile'):
   rec=row[typ];checkfile(packet/'attempt01'/(n+'-'+typ+'.txt'),rec['log_sha256']);checkfile(out/(n+'-'+typ+'.txt'),rec['log_sha256'])
   assert not rec['monitor_errors'] and not rec['observed_descendant_pids']
  assert row['deps']['exit']==0 and row['deps']['stop_reason'] is None
  guards(row['direct_guard'])
  for dep,rec in row['dependencies'].items():checkfile(rec['path'],rec['sha256'],rec['realpath'])
  if 'object_sha256' in row:checkfile(out/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
 snapshots.append(state)
a,b=snapshots
assert a['failure']=="RuntimeError('compile failed SharingGateModel')" and a['rows'][0]['compile']['exit']==1 and a['rows'][0]['compile']['stop_reason'] is None
log=(first/'attempt01/SharingGateModel-compile.txt').read_text();assert 'Unknown identifier `Function.update_same`' in log and 'Unknown identifier `Function.update_noteq`' in log
assert b['failure']=="RuntimeError('compile failed SharingSeed38')"
assert [r['module'] for r in b['rows']]==names[:3]
for row in b['rows'][:2]:assert row['compile']['exit']==0 and row['compile']['stop_reason'] is None
assert b['rows'][0]['object_sha256']=='c5e2134d16930bbe2be8734295dcf66ad205b2cb2dc462198ae33054a85280dc'
assert b['rows'][1]['object_sha256']=='085639f8f95d4929a0851b4fb2fb8abb68f1cda4a1ee8645dadbcaa92b421b6b'
assert b['rows'][2]['compile']['exit']==-15 and b['rows'][2]['compile']['stop_reason']=='timeout' and b['rows'][2]['compile']['timeout_seconds']==120
assert (retry/'attempt01/SharingSeed38-compile.txt').read_bytes()==b''
assert (retry/'attempt01/SharingGateModel-compile.txt').read_text().count('This simp argument is unused:')==2
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_REVIEW_ONLY','first_state_sha256':sha(first/'attempt01/state.json'),'retry_state_sha256':sha(retry/'attempt01/state.json'),'first_outer_author_record_sha256':sha(first/'attempt01/outer-terminal-author-record.json'),'retry_outer_author_record_sha256':sha(retry/'attempt01/outer-terminal-author-record.json'),'recorded_stages':[r['module'] for r in b['rows']],'retry_object_sha256':{r['module']:r['object_sha256'] for r in b['rows'] if 'object_sha256' in r},'seed_stop':'timeout, exit -15','guard_slots_checked':sum(len(r['direct_guard']) for s in snapshots for r in s['rows']),'overlay_links_each':len(a['overlay_links']),'scope':'Retained states/logs/current provider point checks, post-hoc author exit records and exact source diff; no Lean replay or independent outer-session observation.'},indent=2,sort_keys=True))
