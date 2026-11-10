#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-rows-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-rows-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==96808 and o['author_observed_numeric_outer_exit']==1 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign14PrefixRow00')" and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='958ede9bfdd7d77c2474cfdf2ddc8e08cbd654fa9a7bc26c0649a2242caf0201';r,=s['rows'];e=json.loads((p/'source-manifest.json').read_text())['rows'][0];n='Sign14PrefixRow00';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'] and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists()
for phase in ('deps','compile'):
 v=r[phase];log=n+'-'+phase+'.txt';assert v['exit']==(0 if phase=='deps' else 1) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and v['rss_limit_bytes']==4*1024**3 and v['host_floor_bytes']==10*1024**3 and v['timeout_seconds']==120 and sha(a/log)==sha(out/log)==v['log_sha256']==o['logs'][log]
assert r['compile']['peak_session_rss_bytes']==3775078400 and '(kernel) excessive memory consumption detected' in (a/(n+'-compile.txt')).read_text();log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Sign14Prefix.row00_decode' in log and 'Quot.sound, DiophantineConsistency.Sign14Prefix.row00_decode]' in log
dep=r['dependencies']['DiophantineConsistency.Sign14PrefixParser'];assert dep['sha256']=='e0cf8226256f2270c89a52d44173cea37f0d27114903c54bc8f70c45fc714a2f' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for name,pin in o['prefix_sha256'].items():assert sha(a/name)==sha(p/'src/DiophantineConsistency'/name)==sha(out/'src/DiophantineConsistency'/name)==sha(root/'research/nine-sharing-sign14-prefix-formula'/name)==pin
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':96808,'peak_session_rss_bytes':3775078400,'scope':'row00 kernel memory failure and self-referential axiom report; no row00 object, later stages or postflight'},indent=2))
