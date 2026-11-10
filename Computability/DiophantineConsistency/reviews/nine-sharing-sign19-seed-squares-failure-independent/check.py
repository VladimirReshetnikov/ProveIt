#!/usr/bin/env python3
"""Independently inspect the captured sign19 timeout; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2]
packet=root/'research/nine-sharing-sign19-seed-squares-check'
a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign19-seed-squares-check-20261109')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
outer=json.loads((a/'outer-result.json').read_text());assert outer['author_observed_outer_session']==10092 and outer['author_observed_numeric_outer_exit']==1
assert sha(a/'state.json')==outer['state_sha256']=='a1aa9d01545dd569bec724d54c2a2b9a309dd7dd46729dae3c19624e743f2e8e'
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed SharingSeed19Degree44')" and len(s['rows'])==1
assert s['runner_sha256']==sha(packet/'run.py')=='bdd1057e7b5850f3fd1fc3ab0bc1e8399c6ee3d894eeffcaa9ed97239a1c99d7'
r=s['rows'][0];assert r['module']=='SharingSeed19Degree44' and r['source_sha256']=='549dc7e56092e5bbc4c75fe9a13dd4f94aa144573c71945644fe2f16d5047ded'
assert sha(out/'src/DiophantineConsistency/SharingSeed19Degree44.lean')==sha(packet/'src/DiophantineConsistency/SharingSeed19Degree44.lean')==r['source_sha256']
assert r['deps']['exit']==0 and r['deps']['stop_reason'] is None
c=r['compile'];assert c['exit']==-15 and c['stop_reason']=='timeout' and c['timeout_seconds']==120 and c['peak_session_rss_bytes']==2592022528 and c['min_host_available_bytes']==19026219008 and not c['monitor_errors'] and not c['observed_descendant_pids']
for stage in ('deps','compile'):
 name='SharingSeed19Degree44-'+stage+'.txt';assert sha(a/name)==sha(out/name)==outer['logs'][name]==r[stage]['log_sha256']
assert (a/'SharingSeed19Degree44-compile.txt').read_bytes()==b''
assert not (out/'lib/DiophantineConsistency/SharingSeed19Degree44.olean').exists() and not (out/'lib/DiophantineConsistency/SharingSign19Squares.olean').exists()
for k,v in r['direct_guard'].items():
 p=Path(k)
 if v is None:assert not os.path.lexists(p)
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256']
for k,v in s['overlay_links'].items():
 p=Path(k);assert p.is_symlink() and str(p.resolve())==v
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':10092,'outer_exit':1,'child_exit':-15,'stop_reason':'timeout','guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'No syntax or squares object; no endpoint or final postflight'},indent=2,sort_keys=True))
