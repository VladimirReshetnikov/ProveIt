#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-forward-gap-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-forward-gap-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'736bc577fc222d3abbaecf3ba26eba355ed7cd0ecf9ade9a834fd913ec108a05','Sign33CurrentForwardGap-compile.txt':'9d1ad0363ca973d42807d9ff749cc8346a9c665ecb732051c8937e020d1510a8','outer-observation.json':'4debd61819d1a04afbd8d18f435b9f315023282120c522a566915e75c838fe62'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(91744,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentForwardGap' and r['source_sha256']=='503c4b4347f0f9dcfbbc4aba58a6199e8e5c2c9ad4d4222132ae8e767627e5dd' and r['object_sha256']=='80fd0e2908fd8ab6f5ae47bb768e455510f8c29df4a98287ef01d28e54b7471a'
assert h(p/'src/DiophantineConsistency/Sign33CurrentForwardGap.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentForwardGap.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentForwardGap-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentForwardGap-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('source_has_representatives_and_gap',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentForwardGap\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentCoreCuts':'1f9a7c639979896a0fbdcc8213a6410c83062953c500a9f9beebd1fa1e75812b','DiophantineConsistency.Sign33ForwardGap':'e35f9ca9bc90675ed64d25c28c3abbc4b203ddb3a6e5a3af6abb6e82ab74f795'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1197
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':91744,'direct_guard_slots':150,'overlay_links':1197,'scope':'source representatives and gap under explicit cast; no Lean replay'},sort_keys=True,indent=2))
