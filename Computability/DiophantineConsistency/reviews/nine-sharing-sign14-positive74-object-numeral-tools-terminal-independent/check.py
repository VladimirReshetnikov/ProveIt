#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-object-numeral-tools-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-object-numeral-tools-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==15785 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='3d9883f939ccd34e9e1b62f9118a0acd4981c72e20f52af2d53789c0799731ce'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74ObjectNumeralTools';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert e['imports']==['DiophantineConsistency.Sign14Positive74ObjectMulZeroNative','DiophantineConsistency.IPRAZeroLeft']
prior=json.loads((root/'research/nine-sharing-sign14-positive74-object-mul-zero-native-check/attempt01/state.json').read_text());assert prior['status']=='PASS'
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256'] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 if mod.endswith('MulZeroNative'):assert d['sha256']==prior['rows'][0]['object_sha256']
 if mod.endswith('IPRAZeroLeft'):assert d['sha256']=='1a0a6cece7636fb646b3c259059f103d474cc0a4b81b7e28806e21568d3e6c26'
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(z in log for z in ('zeroLeftOpen','transOpen')) and log.count('[propext, Classical.choice, Quot.sound]')==2 and log.count('warning:')==0 and all(z not in log for z in ('error:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':15785,'stages':1,'scope':'native open zero-left and transitivity; literal one normalization, positive leaf and closure separate'},indent=2))
