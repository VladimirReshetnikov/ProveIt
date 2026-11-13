#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-axis-seed-degree-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-axis-seed-degree-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==23369 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and s['runner_sha256']==sha(p/'run.py')=='9782bac6013dcd255c3946a0a6c36713f0c766041bcdfff687fba7649572cd8d'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];pins={'Sign14AxisNaBinding':'d4cbe8458003e56641e5fb60760f12ae07bd4473dc2bd2d025b49b2b8a21c49d'};warnings=0
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 for mod in e['imports']:
  dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=(a/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log;warnings+=log.count('warning:');pins[n]=r['object_sha256']
assert warnings==2
for n,th in [('Sign14AxisOtherDegree',['other_rows_syntax_degree','other_rows_axis_degree']),('Sign14AxisNoncancel',['other_sum_degree_le','na_square_degree','combined_degree']),('Sign14AxisSeedDegree',['seed_axis','seed_axis_degree'])]:
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(t in log for t in th) and log.count('depends on axioms:')==len(th) and all(x in ('[propext, Quot.sound]','[propext, Classical.choice, Quot.sound]') for x in __import__('re').findall(r'depends on axioms: (\[[^]]+\])',log))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':23369,'stages':3,'warnings':warnings,'scope':'actual staged seed axis natDegree 124 under p0 nonzero; diagonal lower separate'},indent=2))
