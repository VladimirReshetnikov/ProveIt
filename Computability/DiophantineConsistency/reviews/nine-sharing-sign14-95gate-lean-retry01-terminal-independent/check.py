#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-95gate-lean-retry01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-95gate-lean-retry01-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==6531 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='56a2145678fe5294e940101bf868e1ef22ba914a41958c028afdd9b9ce684464'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Optimized95';src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert e['imports']==['DiophantineConsistency.Sign14AbstractExpressionDef','DiophantineConsistency.ModelJonesSyntax']
expected={'DiophantineConsistency.Sign14AbstractExpressionDef':'8cf256a30987633bba738449290b463e7082869d2e69456982006b59b9813c54','DiophantineConsistency.ModelJonesSyntax':'ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==expected[mod] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Sign14Optimized95.seed_eval' in log and '[propext, Quot.sound]' in log and 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==5 and log.count('warning: This simp argument is unused:')==5
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':6531,'stages':1,'scope':'optimized seed evaluation equals prior staged seed in arbitrary commutative rings; degree/iPRA/JSON/PDF separate'},indent=2))
