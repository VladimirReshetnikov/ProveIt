#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-first-cut-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-first-cut-retry01-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'e4a8cac08edb420ebbbc5ab1d77fa8e553037aba3fcf46498ab40adec0c1ea3f','Sign33FirstCut-compile.txt':'8aefccde2a61c5fb3b43f5fcdcf7d7120fed8018eb1233dcb9ff96747b172fd0','outer-observation.json':'11380a0a8d85a73d3a5a96a3bed71ef9083288e90e8538f9e19d83e99e1c1986'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(5046,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33FirstCut' and r['source_sha256']=='57cc9442200276eb3e15fb659ea4a729f213e22f1ab17e7402136a7ad8f4e962' and r['object_sha256']=='65bdf051fa81c881099198b4b46e17f4cccb05e0c9e373e977c3502b0ff310ae'
assert h(p/'src/DiophantineConsistency/Sign33FirstCut.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33FirstCut.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33FirstCut-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33FirstCut-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('first_residual_eval','first_cut_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33FirstCut\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1173
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':5046,'direct_guard_slots':100,'overlay_links':1173,'scope':'single same-valuation q-square cut; no Lean replay'},sort_keys=True,indent=2))
