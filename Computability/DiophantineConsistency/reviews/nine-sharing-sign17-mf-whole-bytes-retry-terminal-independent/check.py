#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-mf-whole-bytes-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-mf-whole-bytes-retry-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();outer=json.loads((a/'outer-result.json').read_text());assert outer=={'outer_session':25893,'outer_exit_code':1}
assert sha(a/'state.json')==sha(out/'state.json');st=json.loads((a/'state.json').read_text());assert st['status']=='FAILED' and st['failure']=="RuntimeError('compile failed Sign17MFWholeBytes')" and len(st['rows'])==23 and st['runner_sha256']==sha(p/'run.py')=='4241b9bccc3feafcdf7e628ee5fe5f0b3dd979e837b208c3c9607b335ad0a826'
entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==23
for row,e in zip(st['rows'],entries):
 n=row['module'];assert e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==row['source_sha256']==e['source_sha256']
 assert row['deps']['exit']==0 and row['deps']['stop_reason'] is None
 for key in ('deps','compile'):
  phase=row[key];assert sha(out/(n+'-'+key+'.txt'))==phase['log_sha256'];assert phase['rss_limit_bytes']==4*1024**3 and phase['host_floor_bytes']==10*1024**3 and phase['timeout_seconds']==120 and not phase['monitor_errors'] and not phase['observed_descendant_pids']
 if n!='Sign17MFWholeBytes':
  assert row['compile']['exit']==0 and row['compile']['stop_reason'] is None and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==row['object_sha256'];log=(out/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log
 else:
  assert row['compile']['exit']==1 and row['compile']['stop_reason'] is None and 'object_sha256' not in row and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists();log=(a/'compile.txt').read_text();assert 'unsolved goals' in log and 'List.replicate 909' in log and '[] ++' in log and 'sorryAx' in log;assert sha(a/'compile.txt')==row['compile']['log_sha256'] and sha(a/'deps.txt')==row['deps']['log_sha256']
for path,target in st['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':25893,'outer_exit':1,'successful_children':22,'failure_child_exit':1,'scope':'MF digits/block list equality failed; no whole-byte object or final postflight'},indent=2))
