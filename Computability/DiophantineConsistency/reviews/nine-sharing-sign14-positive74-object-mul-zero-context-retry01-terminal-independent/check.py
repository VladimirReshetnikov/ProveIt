#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-positive74-object-mul-zero-context-retry01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-positive74-object-mul-zero-context-retry01-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==88139 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='e017fe396668b07d219feb405b3beb06c5665bbfd1806abc181053495d800492'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14Positive74ObjectMulZeroContext';src=p/'src/DiophantineConsistency'/(n+'.lean');assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
assert e['imports']==['DiophantineConsistency.Sign14Positive74ObjectShiftPartial','DiophantineConsistency.IPRAAddOneDirect']
prior=json.loads((root/'research/nine-sharing-sign14-positive74-object-shift-partial-check/attempt01/state.json').read_text());assert prior['status']=='PASS'
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256'] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 if mod.endswith('ShiftPartial'):assert d['sha256']==prior['rows'][0]['object_sha256']
 if mod.endswith('IPRAAddOneDirect'):assert d['sha256']=='34016e7d69ee2a8a1c7ed44132ef49b9b9cacf06c4117625c543885d26df32c3'
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'mul_zero' in log and log.count('[propext, Classical.choice, Quot.sound]')==1 and log.count('warning:')==1 and all(z not in log for z in ('error:','sorryAx'))
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':88139,'stages':1,'scope':'finite-context multiplication-zero under explicit Δ; nativeTheory discharge separate'},indent=2))
