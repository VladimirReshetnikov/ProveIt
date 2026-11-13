#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-endpoint-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-dag-endpoint-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==26270 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='ef7856801fc25a2b71069d40370cb6cb6641499ea6f32a5695b9a7cf4a7ba7f3'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14PrefixDagEndpoint';src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
base=json.loads((root/'research/nine-sharing-sign14-prefix-dag-degree-retry01-check/attempt01/state.json').read_text());endpoint=json.loads((root/'research/nine-sharing-sign14-endpoint-check/attempt01/state.json').read_text());assert e['imports']==['DiophantineConsistency.Sign14PrefixDagDegree','DiophantineConsistency.Sign14DirectNoAliasTranslated']
expected={'DiophantineConsistency.Sign14PrefixDagDegree':base['rows'][0]['object_sha256'],'DiophantineConsistency.Sign14DirectNoAliasTranslated':endpoint['rows'][2]['object_sha256']}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==expected[mod] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
for row in endpoint['rows']:
 name=row['module'];q=out/'lib/DiophantineConsistency'/(name+'.olean');orig=Path('/tmp/nine-sharing-sign14-endpoint-check-20261110/lib/DiophantineConsistency')/(name+'.olean');assert q.is_symlink() and str(q.resolve())==str(orig.resolve()) and sha(q)==row['object_sha256'] and s['overlay_links'][str(q)]==str(orig.resolve())
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all('Sign14PrefixDagCurrent.'+name in log for name in ('native_equivalence','standard_equivalence','standard_translated_equivalence')) and log.count('[propext, Classical.choice, Quot.sound]')==3 and all(t not in log for t in ('error:','warning:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':26270,'stages':1,'scope':'native/standard/translated iPRA endpoint for embedded fragment-DAG symbolic expression; file/JSON/PDF relation external'},indent=2))
