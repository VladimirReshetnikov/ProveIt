#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-probe-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-probe-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==33475 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2 and s['runner_sha256']==sha(p/'run.py')=='5d62bfa707d05f350dae4a2ff30ce75ec20e2e267cf3fc245ccdc40a613daea0'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];pins={'SharingSeed14Degree124':'e963bf6ea3b84831c90eda3bd7568fbc4e4658774f98bb7907b0f4917b15c20e'};warnings=0
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
assert warnings==0
log=' '.join((a/'Sign14PrefixRow02-compile.txt').read_text().split());assert 'Sign14Prefix.row02_decode' in log and log.count('[propext, Classical.choice, Quot.sound]')==1
for q in (p/'src/DiophantineConsistency/row02.prefix',out/'src/DiophantineConsistency/row02.prefix',root/'research/nine-sharing-sign14-prefix-formula/row02.prefix'):assert sha(q)=='5ee89dc23b452dbc19fbc67a6c0a8ffab029ed8dab27aa8b597e6987f9648c06' and len(q.read_bytes())==51
assert 'decode p 24 (include_str "row02.prefix").toList =' in (p/'src/DiophantineConsistency/Sign14PrefixRow02.lean').read_text()
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':33475,'stages':2,'warnings':warnings,'scope':'embedded 51-byte Nt row prefix decodes to actual staged row; JSON/PDF binding separate'},indent=2))
