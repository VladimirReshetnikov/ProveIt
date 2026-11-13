#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-core-norms-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-core-norms-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'c3fd69521bec9a0b77c673c8c69ed03653c1fa60b6fd3d54b6c48963d1842ac7','Sign33CurrentCoreNorms-compile.txt':'079c24aae77808a0a9f708b2d6c5b8b409f195aa56020b865f9ee2553fbde083','outer-observation.json':'0c1f61d701e75c705d762fd800a54530c7251c1c7ecf2256adad7e1df707188a'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(34241,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentCoreNorms' and r['source_sha256']=='703dfba0e5abb9719cca4dee5455a94234bad3688ef4e25050701644b3333fd8' and r['object_sha256']=='494d28f41ea9767d30216bfe5dd4e13026fb10d89cc1559b9ec8d4c8bee62d49'
assert h(p/'src/DiophantineConsistency/Sign33CurrentCoreNorms.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentCoreNorms.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentCoreNorms-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentCoreNorms-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('source_core_norms',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentCoreNorms\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Norm38FixedPortNorms':'2cfd83ff77fbe9ffe28d9f37b61c2f3c374b59d9aefdce9c28dad55cad11bd7c','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':34241,'direct_guard_slots':150,'overlay_links':1194,'scope':'current shifted source zero implies core norms; no Lean replay'},sort_keys=True,indent=2))
