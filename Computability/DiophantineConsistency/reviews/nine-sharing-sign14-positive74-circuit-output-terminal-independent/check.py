#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-output-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-circuit-output-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==67888 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='ace15c886b5c1c0ece98c5d94a868a0f75d8af825931beba44d04a133fa45766'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74CircuitOutput';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for name in e['imports']:
 d=r['dependencies'][name];q=Path(d['path']);assert q.is_file() and str(q.resolve())==d['realpath'] and sha(q)==d['sha256'] and r['direct_guard'][str(q)]=={'sha256':d['sha256'],'realpath':d['realpath']};prior=json.loads((root/'research/nine-sharing-sign14-positive74-circuit-transitions-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][-1]['object_sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(z in log for z in ('circuitExpr_eq','circuitEval_eq')) and log.count('[propext]')==2 and all(z not in log for z in ('error:','warning:','sorryAx'))
for f in ('nine-sharing-sign14-positive74-circuit-output-source-independent','nine-sharing-sign14-positive74-circuit-transitions-terminal-independent','nine-sharing-sign14-positive74-circuit-retry01-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':67888,'scope':'state74 register73 symbolic and arbitrary commutative-ring output equals positive74 expression; external file binding separate'},indent=2))
