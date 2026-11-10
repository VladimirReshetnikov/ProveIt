#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-literal-coefficient-union-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-literal-coefficient-union-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o=={'outer_session':53810,'outer_exit_code':0,'observed_console':'PASS K in-Lean literal coefficient recipe'};assert sha(a/'state.json')==sha(out/'state.json')=='ad827195689acf8785acbabc16c3902381be5e3e9055b28837a9a51da81a6656';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==9 and s['manifest_sha256']==sha(p/'source-manifest.json')
entries=json.loads((p/'source-manifest.json').read_text())['rows'];sizes=[96,224,352,480,608,736,864,942]
for i,r in enumerate(s['rows']):
 n=r['module'];e=entries[i];assert e['module'].split('.')[-1]==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
 for ph in ('deps','compile'):
  z=r[ph];log=out/(n+'-'+ph+'.txt');assert sha(log)==z['log_sha256'] and z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'] and z['rss_limit_bytes']==4*1024**3 and z['host_floor_bytes']==10*1024**3 and z['timeout_seconds']==120
  if i==8:assert sha(a/log.name)==sha(log)
 if i<8:assert n=='Sign17KTileCoeffUnion'+str(sizes[i])
 else:assert n=='Sign17KLiteralCoefficients'
 obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256'];text=(out/(n+'-compile.txt')).read_text();assert 'sorryAx' not in text and 'error:' not in text and text.count('depends on axioms')==(1 if i==0 else (3 if i==8 else 2))
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/'Sign17KLiteralCoefficients-compile.txt').read_text().split());assert all(('Sign17KLiteralCoefficients.'+x) in log for x in ('coefficients_eq_literal','rawWord_literal','K_literal')) and log.count('[propext, Classical.choice, Quot.sound]')==3 and 'warning:' not in log
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':53810,'stages':9,'scope':'in-Lean Fin986 coefficient literal and rawWord/K identities; external JSON/gzip/file binding separate'},indent=2))
