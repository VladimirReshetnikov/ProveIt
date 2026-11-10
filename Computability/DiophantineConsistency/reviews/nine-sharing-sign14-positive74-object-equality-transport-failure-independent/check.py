#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-object-equality-transport-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-object-equality-transport-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==94354 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14Positive74ObjectEqualityTransport')" and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='18f7d1cab46ea62acd34fd4926f9113f8d13182f18cfcc8fb19ba1416ebb8041'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74ObjectEqualityTransport';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and 'object_sha256' not in r
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(0 if ph=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftFull','DiophantineConsistency.IPRADifferenceStepClosure']
prior=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-full-check/attempt01/state.json').read_text());assert prior['status']=='PASS'
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256'] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 if mod.endswith('ShiftFull'):assert d['sha256']==prior['rows'][0]['object_sha256']
 if mod.endswith('IPRADifferenceStepClosure'):assert d['sha256']=='44cf530a6a9f86455bd55583c0753559c5fccb403a9b8666e336d39db4599f94'
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert log.count('error: Type mismatch')==2 and 'Rew.embSubsts' in log and log.count('sorryAx')==2 and all(z in log for z in ('equalityForward','equalityBackward'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':94354,'stages':1,'scope':'two equality-atom substitutions fail finite vector rewrites; both reports sorryAx, no object'},indent=2))
