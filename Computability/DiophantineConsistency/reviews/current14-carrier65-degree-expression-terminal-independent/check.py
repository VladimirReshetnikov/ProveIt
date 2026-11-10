#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-degree-expression-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-degree-expression-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==24191 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Current14Carrier65DegreeExpression';assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'] and 'Init' in r['dependencies']
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
 if mod.endswith('DegreeDirect'):
  prior=json.loads((root/'research/current14-carrier65-degree-direct-retry-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][1]['object_sha256']
 if mod.endswith('CurrentEquationSyntax2011'):assert d['sha256']=='28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae'
 if mod.endswith('WeightedExpressionDegree'):assert d['sha256']=='948b4e01db000ecf59395fc5555f51bf4b249f8922c40f40bbd6585b190b5772'
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(z in log for z in ('expression_eq_polynomial','expression_exact')) and log.count('[propext, Classical.choice, Quot.sound]')==2 and log.count('warning:')==0 and not any(z in log for z in ('error:','sorryAx'))
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':24191,'scope':'in-Lean expressionAt p exact degree 150 for p0 nonzero; current specialization/PDF separate'},indent=2))
