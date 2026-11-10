#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-degree-identity-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-degree-identity-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==34532 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='476a3114869b2035d789d023c661bae3db90e87699c6f515457ad39347a46e80'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74DegreeIdentity';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for name in e['imports']:
 d=r['dependencies'][name];q=Path(d['path']);assert q.is_file() and str(q.resolve())==d['realpath'] and sha(q)==d['sha256'] and r['direct_guard'][str(q)]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'shifted_polynomial' in log and log.count('[propext, Classical.choice, Quot.sound]')==1 and all(z not in log for z in ('error:','warning:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for f in ('nine-sharing-sign14-positive74-object-endpoint-terminal-independent','nine-sharing-sign14-positive74-expression-bridge-terminal-independent','nine-current-lightweight-jones-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],check=True,capture_output=True,timeout=180)
f=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(p/'framework-survey.py')],check=True,capture_output=True,text=True,timeout=180).stdout);assert f['status']=='PASS' and f['observed']['Sign14Positive74ExpressionBridge']['sha256']==r['dependencies']['DiophantineConsistency.Sign14Positive74ExpressionBridge']['sha256'] and f['observed']['ModelCoding']['sha256']==r['dependencies']['DiophantineConsistency.ModelCoding']['sha256']
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':34532,'scope':'positive74 polynomial translated by x+1 equals natural86 polynomial, arbitrary integer ports; external graph and degree separate'},indent=2))
