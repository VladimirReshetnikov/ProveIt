#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-digit-bound-probe-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-digit-bound-probe-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':25029,'outer_exit_code':0} and sha(a/'state.json')==sha(out/'state.json')=='d11659181ffa5c24e9bd3ba5111394ebb4979eb12b119e15a367667863cb62e3';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r,=s['rows'];n=r['module'];assert n=='Sign17KDigitBoundProbe';e,=json.loads((p/'source-manifest.json').read_text())['rows'];assert e['source_sha256']==r['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
for phase in ('deps','compile'):
 x=r[phase];name=n+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256'];log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(('Sign17KDigitBoundProbe.'+x) in log for x in ('stream_bound','first_block_bound','tail_block_bound','control_block_bound')) and log.count('[propext, Classical.choice, Quot.sound]')==3 and log.count('[propext, Quot.sound]')==1 and all(x not in log for x in ('error:','warning:','sorryAx'))
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':25029,'scope':'conditional stream bound and 90 sample coefficient bounds only; no K/file theorem'},indent=2))
