#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-node78-factor-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-node78-factor-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'c59906a32aa1a905544c2bac4b791f4fa76d7bc179fd8ba1ccb83feb9a4261c3','Sign33Node78Factor-compile.txt':'7b738f9d90e7b4416a16cb44e51fdfc16522bc53f9c9f4c34c692ac4100ade4f','outer-observation.json':'cba9104115ad049b0457a960db4c8034b26f8f49b95d3d766ca2541cfdd9e3a5'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(41506,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33Node78Factor' and r['source_sha256']=='4b55772f4ce4f7fb71a38a649183144c3e032150c29f0c4330009581acb74577' and r['object_sha256']=='6fdc177f8aece228d1c1f44d0cb75403a69e864342536ec25128d9ce9819ec18'
assert h(p/'src/DiophantineConsistency/Sign33Node78Factor.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33Node78Factor.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33Node78Factor-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33Node78Factor-compile.txt').read_text();assert log.count('warning:')==1 and 'error:' not in log and 'sorryAx' not in log
for t in ('node78',):assert re.search(r"'DiophantineConsistency\.Sign33Node78Factor\."+t+r"' depends on axioms: \[propext,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':41506,'direct_guard_slots':100,'overlay_links':1194,'scope':'generic static node78 factor; no Lean replay'},sort_keys=True,indent=2))
