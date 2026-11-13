#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-lines-current14-endpoint-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-lines-current14-endpoint-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':97973,'outer_exit_code':0}
assert sha(a/'state.json')==sha(out/'state.json')=='f5266c1f80b721ac36a252418b1cee78ed26281e06f15020d910273be60ccde7'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['manifest_sha256']==sha(p/'source-manifest.json')
e=json.loads((p/'source-manifest.json').read_text())['rows'][0];r=s['rows'][0];n='Sign17LinesCurrent14Endpoint';assert r['module']==n and e['module']=='DiophantineConsistency.'+n
assert sha(root.parents[1]/e['source'])==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all('Sign17LinesCurrent14Endpoint.'+x in log for x in ('linePorts_eq','linePorts_recipes','line_endpoint','line_endpoint_translated')) and log.count('[propext, Classical.choice, Quot.sound]')==4 and all(x not in log for x in ('error:','warning:','sorryAx'))
prior=json.loads((root/'research/nine-sharing-sign17-literal-ports-replay-check/attempt01/state.json').read_text());assert prior['status']=='PASS';base=Path('/tmp/nine-sharing-sign17-literal-ports-replay-20261110/lib/DiophantineConsistency');pins={'Sign17LinesKernel':'0a921c9ad6aa56e398724c75c2ce03c0667a5fa2470696c6872659d50a0156d0','IPRAStandardCurrentEndpoint':'3b8abcafa1fad691d9a9005e2af8afae8bda77c7d761a00119ccea1c742dcbd2'}
for name,pin in pins.items():
 d=r['dependencies']['DiophantineConsistency.'+name];z=base/(name+'.olean');assert str(z) in prior['overlay_links'] and str(z.resolve())==prior['overlay_links'][str(z)]==d['realpath'] and sha(z)==d['sha256']==pin and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
d=r['dependencies']['DiophantineConsistency.Sign17LiteralPorts'];z=base/'Sign17LiteralPorts.olean';assert str(z.resolve())==d['realpath'] and sha(z)==d['sha256']==prior['rows'][0]['object_sha256'] and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':97973,'scope':'numeral-K current14 ports and two standard iPRA equivalences; no PDF/file/full ancestry theorem'},indent=2))
