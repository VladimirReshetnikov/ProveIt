#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-dag-value-congr-diagnostic-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-dag-value-congr-diagnostic-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==1035 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-failure-independent/check.py')],capture_output=True,check=True,timeout=180)
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Current14Carrier65DAGValue';assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
old=json.loads((root/'research/current14-carrier65-dag-check/attempt01/state.json').read_text());assert old['status']=='FAILED' and len(old['rows'])==3
assert 'Init' in r['dependencies']
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
 if mod.endswith('DAGCore'):assert d['sha256']==old['rows'][1]['object_sha256']
 if mod.endswith('Carrier65'):assert d['sha256']=='10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f'
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Current14Carrier65DAG.value_eq_carrier' in log and log.count('[propext]')==1 and log.count('warning:')==3 and 'error:' not in log and 'sorryAx' not in log and 'congr 1' in log
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':1035,'scope':'arbitrary-ring circuit evaluator equals Carrier65.value, using successful circuit children of failed parent'},indent=2))
