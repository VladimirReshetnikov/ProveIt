#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-circuit-transitions-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-circuit-transitions-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==8227 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==9 and s['runner_sha256']==sha(p/'run.py')=='c89d5c4900c6b4628eb1f4fe47eaebce2d20c510c9cceab3c7011587fbe64158'
es=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(es)==9;built={}
for i,(e,r) in enumerate(zip(es,s['rows'])):
 n=f'Sign14Positive74CircuitTransitions{i:02}';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 dep,=e['imports'];d=r['dependencies'][dep];q=Path(d['path']);assert q.is_file() and str(q.resolve())==d['realpath'] and sha(q)==d['sha256'] and r['direct_guard'][str(q)]=={'sha256':d['sha256'],'realpath':d['realpath']}
 if i>0:assert d['sha256']==built[i-1] and q.resolve()==(out/'lib/DiophantineConsistency'/f'Sign14Positive74CircuitTransitions{i-1:02}.olean').resolve()
 else:
  prior=json.loads((root/'research/nine-sharing-sign14-positive74-circuit-transition-probe-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][0]['object_sha256']
 built[i]=r['object_sha256'];log=' '.join((a/(n+'-compile.txt')).read_text().split());end=min(11+8*i,74);assert f'symState{end}' in log and f'numState{end}' in log and log.count('[propext]')==2 and all(z not in log for z in ('error:','warning:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
for f in ('nine-sharing-sign14-positive74-circuit-transitions-source-independent','nine-sharing-sign14-positive74-circuit-transition-probe-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':8227,'scope':'all 74 symbolic and arbitrary-ring register states through 9 stages; final output equality and external file binding separate'},indent=2))
