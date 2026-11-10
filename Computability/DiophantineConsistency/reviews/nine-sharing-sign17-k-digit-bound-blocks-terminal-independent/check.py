#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-digit-bound-blocks-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-digit-bound-blocks-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert json.loads((a/'outer-result.json').read_text())=={'outer_session':82107,'outer_exit_code':0} and sha(a/'state.json')==sha(out/'state.json')=='4bfa9dd1b8fffc362f0ac39479ac3ce7e8b14f02dcc3d86eb51266d2563a2696';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==14 and s['manifest_sha256']==sha(p/'source-manifest.json');entries=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-radix-stream-current-check/attempt01/state.json').read_text());assert prior['status']=='PASS'
for i,r in enumerate(s['rows'],1):
 n=f'Sign17KDigitBoundBlock{i:02}';e=entries[i-1];assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert n+'.bound' in log and '[propext, Classical.choice, Quot.sound]' in log and all(x not in log for x in ('error:','warning:','sorryAx'))
 d=r['dependencies']['DiophantineConsistency.Sign17KRadixStreamCurrent'];assert d['sha256']==prior['rows'][0]['object_sha256'] and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':82107,'stages':14,'coefficient_count':896,'scope':'14 Fin64 literal coefficient bounds only; full assembly and file binding separate'},indent=2))
