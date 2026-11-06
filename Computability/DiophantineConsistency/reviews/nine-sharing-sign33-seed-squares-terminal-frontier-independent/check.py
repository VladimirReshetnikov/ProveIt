#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-squares-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-seed-squares-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'b1baa34a7e28603de20eb013e1b6b14e456c3d1ea982cb72a2216ff90a1a1ab0','SharingSign33Squares-compile.txt':'f6e3b8c2e42895d134ee81f808977de920d77fa8f6e8ab1451f67d9b81f1f115','outer-observation.json':'52d69c6a879bff67f3d1fb044d4e3093af14510bb315fbf3da3a61ee76b15fb6'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(54762,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='SharingSign33Squares' and r['source_sha256']=='da2b90143d1452756d9ea24612126e06cf38ae93a9c22cbab4e322d19ac5b190' and r['object_sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42'
assert h(p/'src/DiophantineConsistency/SharingSign33Squares.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/SharingSign33Squares.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('SharingSign33Squares-'+k+'.txt'))==x['log_sha256']
log=(a/'SharingSign33Squares-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('squareSum_nonneg','squareSum_zero_iff','seed_zero_iff_residuals'):assert re.search(r"'DiophantineConsistency\.SharingSign33Squares\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSeed33Syntax'];assert dep['sha256']=='d8d70064be0d7fa609b92a8b51648b6e817096886e0671f37d64271f05e21be0' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1056
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
review=d/'reviews/nine-sharing-sign33-seed-syntax-frontier-independent/check.py';assert h(review)=='934ac9b2b352d19a8b0cef7d04f40270a44fd4a9e428dc50df7bc05123a3a245';subprocess.run([sys.executable,'-I','-S','-B',str(review)],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'status':'PASS','author_recorded_outer_session':54762,'direct_guard_slots':100,'overlay_links':1056,'scope':'same-valuation symbolic-port zero iff residual zeros; no Lean replay'},sort_keys=True,indent=2))
