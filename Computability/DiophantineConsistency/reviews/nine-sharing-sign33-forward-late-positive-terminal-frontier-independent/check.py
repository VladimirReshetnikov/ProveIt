#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-late-positive-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-late-positive-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'07b8243a8bb46e1165707e80fc149a90bc8c12b30de6b5ba38f5b68d361fbec7','Sign33ForwardLatePositive-compile.txt':'eafadfdb24c5232dd296281fec9152f39e9ae08084c9c23f5cd651303a365901','outer-observation.json':'9300f68f9477b49a931e7c81fba1eb6d07afb515bb621bd5c30626fd1cbc1a3e'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(94217,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardLatePositive' and r['source_sha256']=='ba221c995acbb20b4bd19ecc3149b96f8b0c922c2caf0f5941a898ca7d47fa13' and r['object_sha256']=='8d8150a645d643d763cf3fb3e29dfa2bf31f1eb163dcb6a1a96e05f7dd38554d'
assert h(p/'src/DiophantineConsistency/Sign33ForwardLatePositive.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardLatePositive.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardLatePositive-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardLatePositive-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('constructor_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardLatePositive\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':94217,'direct_guard_slots':150,'overlay_links':1194,'scope':'three late positive forward cut equations only; no Lean replay'},sort_keys=True,indent=2))
