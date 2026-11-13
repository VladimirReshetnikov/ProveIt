#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-reflection-retry01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-reflection-retry01-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==4981 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14PrefixReflection')" and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='5cdcab504fdc3e364ac86ecb89a81696c6461b120d7cb4fa71ce24c8b1717349';r,=s['rows'];e=json.loads((p/'source-manifest.json').read_text())['rows'][0];n='Sign14PrefixReflection';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
for phase in ('deps','compile'):
 z=r[phase];log=n+'-'+phase+'.txt';assert z['exit']==(0 if phase=='deps' else 1) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'] and sha(a/log)==sha(out/log)==z['log_sha256']==o['logs'][log]
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/(n+'-compile.txt')).read_text();assert log.count('error: `simp` made no progress')==3 and 'sorryAx' in log
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':4981,'outer_exit':1,'scope':'generic reflection three no-progress Option simplification errors; no object or postflight'},indent=2))
