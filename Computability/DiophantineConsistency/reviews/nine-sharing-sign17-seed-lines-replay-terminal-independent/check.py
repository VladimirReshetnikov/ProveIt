#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-seed-lines-replay-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-seed-lines-replay-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':99576,'outer_exit_code':0}
assert sha(a/'state.json')==sha(out/'state.json')=='f2188ba1494d21fdb1fa8502872b321fa6e603cef2bd295a4282e695a908aa52'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['manifest_sha256']==sha(p/'source-manifest.json')
e=json.loads((p/'source-manifest.json').read_text())['rows'][0];r=s['rows'][0];n='Sign17SeedLines';assert r['module']==n and e['module']=='DiophantineConsistency.'+n
assert sha(root.parents[1]/e['source'])==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'decimal_lines_eq_seed' in log and log.count('does not depend on any axioms')==1 and all(x not in log for x in ('error:','warning:','sorryAx'))
prior=json.loads((root/'research/nine-sharing-sign17-k-byte-binding-retry-check/attempt01/state.json').read_text());assert prior['status']=='PASS';d=r['dependencies']['DiophantineConsistency.DecimalMachine215'];base=Path('/tmp/nine-sharing-sign17-k-byte-binding-retry-20261110/lib/DiophantineConsistency/DecimalMachine215.olean');assert str(base) in prior['overlay_links'] and str(base.resolve())==prior['overlay_links'][str(base)]==d['realpath'] and sha(base)==d['sha256']=='9a28850ecd82e97bbc7361ec39820edc4abe8473a62f08079a1da34fdd462687' and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':99576,'scope':'twelve explicit digit lines decode to Lean seed; no PDF or full ancestry theorem'},indent=2))
