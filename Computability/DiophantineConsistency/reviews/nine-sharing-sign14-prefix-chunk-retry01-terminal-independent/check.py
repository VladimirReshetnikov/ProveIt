#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-chunk-retry01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-chunk-retry01-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==77531 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14PrefixChunk00')" and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='c73998d905def146404e96811e113e9edbfac0c9cbb3d2f5ac3d5d0e4e6e4ee4';r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14PrefixChunk00';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(0 if ph=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/(n+'-compile.txt')).read_text();assert log.count('error: (kernel) excessive memory consumption detected')==1 and 'Sign14PrefixChunk00.shared07_bytes' in log and log.count('Sign14PrefixChunk00.file_head')==2
for q in (p/'src/DiophantineConsistency/row00.prefix',out/'src/DiophantineConsistency/row00.prefix',root/'research/nine-sharing-sign14-prefix-formula/row00.prefix'):assert sha(q)==o['prefix_sha256']=='a9d8d3ec099bb64b6146234f605488d1e3d8091666e3a9c9f7507d86b9574bf6' and len(q.read_bytes())==689
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':77531,'outer_exit':1,'peak_rss':r['compile']['peak_session_rss_bytes'],'scope':'first file-head proof kernel memory failure with self-dependent report, no object/postflight'},indent=2))
