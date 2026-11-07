#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ipra-endpoint-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ipra-endpoint-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'451878b602e716cd712c2e8709e3546c13e5dbcc7c1ff7edc6dc669b640a4338','Sign33IPRAEndpoint-compile.txt':'97584f5611e99457acc7a9e2e0c8999dee853d459de840056afe041c20b60708','outer-observation.json':'947c97702c9f7c5e4b8772ea464cfb3601adb2bd7977338b5e5a720a08631a3b'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(53823,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33IPRAEndpoint' and r['source_sha256']=='76f72845b8171f09820080be06733560c18a31230573892614b532f11d65c0fd' and r['object_sha256']=='a6fa32adea62053f1ad4e1d0db809171dd2881e8eacefbba6a43ce5ab21fd80c'
assert h(p/'src/DiophantineConsistency/Sign33IPRAEndpoint.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33IPRAEndpoint.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33IPRAEndpoint-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33IPRAEndpoint-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('zero_iff_current','polynomialBridge','native_equivalence','standard_equivalence','standard_translated_equivalence'):assert re.search(r"'DiophantineConsistency\.Sign33IPRAEndpoint\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentJonesSourceIff':'dc8f78ec59c2030ff3af9d3eb709bca470f7f86e76afad79fc1ba7f001434d34','DiophantineConsistency.HACurrentEquation2011':'139adc47e8f48eee0df7fe0ab7f996dd675967473e764fdd9036e8d9fab6e6d1','DiophantineConsistency.IPRAExpressionNative':'9c2c741dd39fceb7a12eec69b4a038e33d7b9396d0df9ba4207a97ef7254e684','DiophantineConsistency.IPRAStandardTheory':'b2417583564a1d6b0bbfb4952587db79339fab8c2b4d24442145e39578173e19'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==250 and len(s['overlay_links'])==1266
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':53823,'direct_guard_slots':250,'overlay_links':1266,'scope':'symbolic nine Jones native and standard iPRA equivalences; no Lean replay'},sort_keys=True,indent=2))
