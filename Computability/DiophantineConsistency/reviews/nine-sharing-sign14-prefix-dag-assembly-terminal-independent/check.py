#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-assembly-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-dag-assembly-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==33671 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='f39092d50bfcd79a0bb6dd9d9452e7d409b2621ac72203037e97c0081f48a6e8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14PrefixDagAssembly';src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
base=json.loads((root/'research/nine-sharing-sign14-prefix-dag-decode-check/attempt01/state.json').read_text());assert e['imports']==['DiophantineConsistency.Sign14PrefixDagDecode04','DiophantineConsistency.Sign14AbstractExpressionDef']
expected={'DiophantineConsistency.Sign14PrefixDagDecode04':base['rows'][4]['object_sha256'],'DiophantineConsistency.Sign14AbstractExpressionDef':'8cf256a30987633bba738449290b463e7082869d2e69456982006b59b9813c54'}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==expected[mod] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Sign14PrefixDagAssembly.seed_eq' in log and 'Sign14PrefixDagAssembly.expression_eq' in log and log.count('[propext, Classical.choice, Quot.sound]')==2 and all(t not in log for t in ('error:','warning:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':33671,'stages':1,'scope':'embedded fragment-DAG expression equals symbolic Fin14 expression; original file/JSON/PDF remains external'},indent=2))
