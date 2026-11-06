#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates00-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates00-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'8d7e080544db4a57a2854f266f299d4e5cae70d1f942b7a5660cf74353b81af5','Sign33RingGates00-compile.txt':'489361d7f6b8e7ac3f3229ca9258a777a3d0443140108d8b430dedcb2bf10da2','outer-observation.json':'3b3ca407f0a6a2f60a569ef3d67501fdfdaf42ee1de98b510b5ba81b6c27e67b'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(36643,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates00' and r['source_sha256']=='25a4150e676deee3d011394e07efa399649bf25a2eca94d1266205f09d5029cf' and r['object_sha256']=='5f9e5ed291cd47de60310e64cab659d1a2f4e2e72d5cd1fe99e5964d0adb3065'
assert h(p/'src/DiophantineConsistency/Sign33RingGates00.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates00.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates00-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates00-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate21','gate22','gate23'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates00\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':36643,'direct_guard_slots':150,'overlay_links':1193,'scope':'three ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
