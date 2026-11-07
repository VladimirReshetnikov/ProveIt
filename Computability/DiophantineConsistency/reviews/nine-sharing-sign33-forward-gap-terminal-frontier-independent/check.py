#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-gap-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-gap-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'f14fcd947acbf345ee0a7cac667d6168794bc830a7ee5870f33e3a7b486a94b9','Sign33ForwardGap-compile.txt':'dbaf69c80fbcc53de7964961cd4f0c314eb1bb471abe37dd982b10698d88bdbc','outer-observation.json':'429729e6d46b002a435930c059e4a0b14f31588171cdf3d541433d65023a5895'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(75897,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardGap' and r['source_sha256']=='aaeb6daee8af6c9a675584899f091fbec537a580aa0aa8b4b17aab58884812a7' and r['object_sha256']=='e35f9ca9bc90675ed64d25c28c3abbc4b203ddb3a6e5a3af6abb6e82ab74f795'
assert h(p/'src/DiophantineConsistency/Sign33ForwardGap.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardGap.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardGap-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardGap-compile.txt').read_text();assert log.count('warning:')==4 and 'error:' not in log and 'sorryAx' not in log
for t in ('gap_of_core',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardGap\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':75897,'direct_guard_slots':200,'overlay_links':1194,'scope':'conditional forward gap cut only; no Lean replay'},sort_keys=True,indent=2))
