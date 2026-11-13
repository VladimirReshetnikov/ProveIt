#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-source-seed-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-source-seed-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'2d3716f0525be2264e28ad8b6715342a4fa29bf8de6130520d2c5dfc8a1fdbe7','Sign33CurrentSourceSeed-compile.txt':'9a4dec2b081e1d21bbd3c30abcfef9c8202f1d8cc55e9f7ffcbbb773b316726d','outer-observation.json':'895c5c52c5a2d9191c4083017e1a5d678905b50da83609d810d5a83bef31811b'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(90994,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentSourceSeed' and r['source_sha256']=='09d79663023756ca3bfa52a7dc518e6d8388ee30fb79e4f5a590c9d8f315c25d' and r['object_sha256']=='df54a0aff1642e5a1fdd46e7c191041917aa276dfbb167b10da5de586ef134c5'
assert h(p/'src/DiophantineConsistency/Sign33CurrentSourceSeed.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentSourceSeed.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentSourceSeed-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentSourceSeed-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('source_implies_seed',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentSourceSeed\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentForwardAllCuts':'f961b85eac605d4429adac9fd17684b9af10fd1ae90b8c8b4a8aa86f6bfd4223','DiophantineConsistency.Sign33ResidualIff':'33eb8b457ea09983d4591856171a37bd8e625dd4cf2d712dbcd621290b5fe204'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1231
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':90994,'direct_guard_slots':150,'overlay_links':1231,'scope':'current natural source zero with port casts implies existential 33 seed zero; no Lean replay'},sort_keys=True,indent=2))
