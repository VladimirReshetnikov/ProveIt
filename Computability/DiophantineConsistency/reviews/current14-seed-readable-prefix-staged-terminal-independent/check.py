#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-seed-readable-prefix-staged-check';a=p/'attempt01';out=Path('/tmp/current14-seed-readable-prefix-staged-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert json.loads((a/'outer-result.json').read_text())=={'outer_session':43837,'outer_exit_code':0} and sha(a/'state.json')==sha(out/'state.json')=='afa41e6b686aba6d0e59cb3a91228cae8d6809bc5b277f4e17cbc7e7b30750b7';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3 and s['manifest_sha256']==sha(p/'source-manifest.json');entries=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-readable-current14-endpoint-check/attempt01/state.json').read_text());assert prior['status']=='PASS';providers={row['module']:row for row in prior['rows']};built={}
for i,r in enumerate(s['rows']):
 n=['Current14QuotedPrefixCore','Current14QuotedPrefixQuote','Current14QuotedPrefixEndpoint'][i];e=entries[i];assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
 log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(x not in log for x in ('error:','warning:','sorryAx'))
 if i==0:assert not log
 if i==1:
  assert log.count('[propext]')==8
  for x in ('reject_reserved','reject_empty','reject_duplicate','reject_unknown','reject_trailing','reject_exhausted','reject_malformed','quotedExpr_eq'):assert 'Current14QuotedPrefix.'+x in log
 if i==2:assert all('Current14QuotedPrefix.'+x in log for x in ('quoteSentence_eq','quoted_endpoint')) and log.count('[propext, Classical.choice, Quot.sound]')==2
 for mod,d in r['dependencies'].items():
  if mod=='Init':continue
  name=mod.split('.')[-1];assert name in providers or name in built;expected=(providers if name in providers else built)[name]['object_sha256'];assert d['sha256']==expected and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
 built[n]=r
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':43837,'stages':3,'scope':'fixed Lean token quotation and selected iPRA endpoint; TeX/PDF/file binding external'},indent=2))
