#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-allcuts-source-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-allcuts-source-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'f7f26e110fb47eeed66c7285139f96c0910be8130d0d004af9afe563610cde8b','Sign33AllCutsSource-compile.txt':'01b4698f44d7605fc4a03e1c11acc0c99e4d6dd4319fd07feca83c6769a81062','outer-observation.json':'fb9234194c0ba98a5b3ac12f33262e119543e76ebb0cc04c382c8077bd9d6214'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(93561,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33AllCutsSource' and r['source_sha256']=='80e80a14f5eb8988912c42bd6a5da35cd0211db130284db69e1d6dcda988b7a2' and r['object_sha256']=='9518aba7d4f0ba9a988284315ace952cbfc8bf6f09865aef1f46ca29d46a5c05'
assert h(p/'src/DiophantineConsistency/Sign33AllCutsSource.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33AllCutsSource.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33AllCutsSource-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33AllCutsSource-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('allcuts_imply_source_zero',):assert re.search(r"'DiophantineConsistency\.Sign33AllCutsSource\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33LiftSourceValue':'272162da4a79b3ab25ac86242ef160ae137447dee9ad0313a6fd2bc845f10acb','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1215
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':93561,'direct_guard_slots':150,'overlay_links':1215,'scope':'AllCuts to generic source zero under four casts; no Lean replay'},sort_keys=True,indent=2))
