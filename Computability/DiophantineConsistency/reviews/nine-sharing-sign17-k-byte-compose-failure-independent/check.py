#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-byte-compose-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-byte-compose-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':55012,'outer_exit_code':1} and sha(a/'state.json')==sha(out/'state.json')=='42b4b2d495159d83a09a4385fbea04270239c890fa9f7a858a4094204c43bd68';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Sign17KByteCompose')" and len(s['rows'])==1;r,=s['rows'];n=r['module'];assert n=='Sign17KByteCompose';e,=json.loads((p/'source-manifest.json').read_text())['rows'];assert e['source_sha256']==r['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
for phase in ('deps','compile'):
 x=r[phase];name=n+'-'+phase+'.txt';assert x['exit']==(0 if phase=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/(n+'-compile.txt')).read_text();assert 'error: Application type mismatch' in log and 'Sign17KByteAlignment00.aligned' in log and 'aligned_append' in log and 'sorryAx' in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':55012,'scope':'compile failed on append association mismatch; sorryAx, no object/postflight'},indent=2))
