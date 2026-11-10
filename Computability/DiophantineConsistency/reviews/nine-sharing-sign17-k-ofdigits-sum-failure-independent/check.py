#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-ofdigits-sum-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-ofdigits-sum-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':97572,'outer_exit_code':1} and sha(a/'state.json')==sha(out/'state.json')=='2f0ca6637c9f43b197781acfd56bdfb528c2228e035739adffc10bc7d0bf25c0';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Sign17KOfDigitsSum')" and len(s['rows'])==1;r,=s['rows'];n=r['module'];assert n=='Sign17KOfDigitsSum';e,=json.loads((p/'source-manifest.json').read_text())['rows'];assert e['source_sha256']==r['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
for phase in ('deps','compile'):
 x=r[phase];name=n+'-'+phase+'.txt';assert x['exit']==(0 if phase=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/(n+'-compile.txt')).read_text();assert 'error: Unnecessary `generalizing` argument' in log and 'depends on axioms' in log and 'sorryAx' not in log
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':97572,'scope':'compile failed despite clean printed axiom report; no object/postflight'},indent=2))
