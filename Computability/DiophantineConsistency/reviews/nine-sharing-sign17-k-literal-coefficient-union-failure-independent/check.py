#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-k-literal-coefficient-union-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-k-literal-coefficient-union-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o=={'outer_session':16571,'outer_exit_code':1};assert sha(a/'state.json')==sha(out/'state.json')=='6328bb93b1adba995fd96f70ee2501a0b88cf5b9821055bc889d12b86534cb55';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['exception']=="RuntimeError('compile failed Sign17KLiteralCoefficients')" and len(s['rows'])==9 and s['manifest_sha256']==sha(p/'source-manifest.json')
entries=json.loads((p/'source-manifest.json').read_text())['rows'];sizes=[96,224,352,480,608,736,864,942]
for i,r in enumerate(s['rows']):
 n=r['module'];e=entries[i];assert e['module'].split('.')[-1]==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256']
 for ph in ('deps','compile'):
  z=r[ph];log=out/(n+'-'+ph+'.txt');assert sha(log)==z['log_sha256'] and z['exit']==(1 if i==8 and ph=='compile' else 0) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'] and z['rss_limit_bytes']==4*1024**3 and z['host_floor_bytes']==10*1024**3 and z['timeout_seconds']==120
  if i==8:assert sha(a/log.name)==sha(log)
 if i<8:
  assert n=='Sign17KTileCoeffUnion'+str(sizes[i]);obj=out/'lib/DiophantineConsistency'/(n+'.olean');assert obj.is_file() and sha(obj)==r['object_sha256'];text=(out/(n+'-compile.txt')).read_text();assert 'sorryAx' not in text and 'error:' not in text
 else:assert n=='Sign17KLiteralCoefficients' and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists()
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(a/'Sign17KLiteralCoefficients-compile.txt').read_text();src=(p/'src/DiophantineConsistency/Sign17KLiteralCoefficients.lean').read_text().splitlines();assert 'maximum recursion depth has been reached' in log and 'congr 1' in src[25] and log.count('sorryAx')==2
part=log.split("'DiophantineConsistency.Sign17KLiteralCoefficients.rawWord_literal'")[0];assert 'coefficients_eq_literal' in part and 'sorryAx' not in part
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':16571,'successful_stages_in_failed_parent':8,'scope':'final compile failed at congr recursion depth; final object/postflight absent; clean pointwise report is not a completed final module'},indent=2))
