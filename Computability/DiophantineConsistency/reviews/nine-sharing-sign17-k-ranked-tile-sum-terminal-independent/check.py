#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-ranked-tile-sum-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-ranked-tile-sum-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==22071 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and sha(p/'run.py')=='4f931bec3cbc40344ca48b1589dba36814da80ce9cd4180a1b8363218f21319d';r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17KRankedTileSum';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==(0 if ph=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/(n+'-compile.txt')).read_text();assert log.count('error: Application type mismatch')==2 and 'Finite.surjective_of_injective' in log and 'candidate_injective' in log and 'sorryAx' in log
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':22071,'outer_exit':1,'scope':'surjectivity application mismatch, sorryAx, no object/postflight'},indent=2))
