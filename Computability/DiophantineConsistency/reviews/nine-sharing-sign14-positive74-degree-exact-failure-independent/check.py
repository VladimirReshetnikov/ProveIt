#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-degree-exact-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-degree-exact-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==13268 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='3494107f574e6db0934c881a1b274a267a8d4f142b80029a111fcb1aba19ad3d'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74DegreeExact';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and 'object_sha256' not in r
for ph,code in (('deps',0),('compile',1)):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for name in e['imports']:
 d=r['dependencies'][name];q=Path(d['path']);assert q.is_file() and str(q.resolve())==d['realpath'] and sha(q)==d['sha256'] and r['direct_guard'][str(q)]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=(a/(n+'-compile.txt')).read_text();assert 'error: Type mismatch' in log and 'MvPolynomial.eval₂ MvPolynomial.C plusOne' in log and '(fun i => MvPolynomial.X i + 1)' in log and 'sorryAx' in log and 'postflight' not in s
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':13268,'scope':'point-free plusOne target mismatch; sorryAx, no object or postflight, no degree theorem established by failed module'},indent=2))
