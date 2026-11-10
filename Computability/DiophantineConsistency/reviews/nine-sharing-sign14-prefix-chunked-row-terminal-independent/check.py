#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-chunked-row-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-chunked-row-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==7881 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14PrefixChunkedRow00')" and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='70a83f3bb2b677f6b3ae4501b1e71ddbe4719de6264001e0d36c5540cca74442';r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign14PrefixChunkedRow00';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(0 if ph=='deps' else -15) and x['stop_reason']==(None if ph=='deps' else 'timeout') and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and (a/(n+'-compile.txt')).read_bytes()==b''
m=json.loads((root/'research/nine-sharing-sign14-prefix-row00-chunks/manifest.json').read_text());assert len(m['chunks'])==22
for e in m['chunks']:
 name=e['file']
 for q in (p/'src/DiophantineConsistency'/name,out/'src/DiophantineConsistency'/name,a/name,root/'research/nine-sharing-sign14-prefix-row00-chunks'/name):assert sha(q)==o['prefix_sha256'][name]==e['sha256'] and len(q.read_bytes())==e['length']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':7881,'outer_exit':1,'elapsed_seconds':r['compile']['elapsed_seconds'],'peak_rss':r['compile']['peak_session_rss_bytes'],'scope':'22-fragment row compile timed out, no object/postflight'},indent=2))
