#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-93gate-degree-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-93gate-degree-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==96321 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='67af0c441bdc0382f7e8555379dc7f7ba396ebdb0d144deefb4283ece39f68c6'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Optimized93Degree';src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert e['imports']==['DiophantineConsistency.Sign14Optimized93Expression','DiophantineConsistency.Sign14Optimized94Degree']
expected={}
for mod,stem in [('DiophantineConsistency.Sign14Optimized93Expression','nine-sharing-sign14-93gate-expression-check'),('DiophantineConsistency.Sign14Optimized94Degree','nine-sharing-sign14-94gate-degree-check')]:
 ps=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert ps['status']=='PASS';expected[mod]=ps['rows'][0]['object_sha256']
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==expected[mod] and Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256'] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
exact=json.loads((root/'research/nine-sharing-sign14-exact-degree-check/attempt01/state.json').read_text());assert len(exact['rows'])==4
for row in exact['rows']:
 name=row['module'];q=out/'lib/DiophantineConsistency'/(name+'.olean');orig=Path('/tmp/nine-sharing-sign14-exact-degree-check-20261110/lib/DiophantineConsistency')/(name+'.olean');assert q.is_symlink() and str(q.resolve())==str(orig.resolve()) and sha(q)==row['object_sha256'] and s['overlay_links'][str(q)]==str(orig.resolve())
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Sign14Optimized93Current.totalDegree_eq' in log and log.count('[propext, Classical.choice, Quot.sound]')==1 and all(t not in log for t in ('error:','warning:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':96321,'stages':1,'scope':'current 93-gate symbolic expression has exact totalDegree 124; file/JSON/PDF relation external'},indent=2))
