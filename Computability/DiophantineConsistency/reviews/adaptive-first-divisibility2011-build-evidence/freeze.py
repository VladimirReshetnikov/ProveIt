from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');O=R/'Computability/DiophantineConsistency/reviews/adaptive-first-divisibility2011-build-evidence';assert not O.exists();O.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
ids=['9vyrj055','i3c7xxg9','te8q_w9p','aj41d8z0','tr_u5so0','niavqmbs','5wet3pp8','rkhdv9mj','z9bdc5ug']
for i,k in enumerate(ids,1):
 p=Path('/tmp/adaptive13-first-divisibility-'+k);q=O/('attempt-%02d'%i);q.mkdir();s=json.loads((p/'state.json').read_text());assert s['status'] in ['PASS','FAILED']
 for f in [p/'state.json',p/'providers.json',p/'driver.py',*sorted((p/'logs').iterdir())]:assert f.is_file() and not f.is_symlink();os.link(f,q/f.name)
a=json.loads((O/'attempt-08/state.json').read_text());b=json.loads((O/'attempt-09/state.json').read_text());assert a['status']==b['status']=='PASS'
for x,y in zip(a['records'],b['records'],strict=True):assert all(x[k]==y[k] for k in ['name','source_sha256','object_sha256','log_sha256'])
shutil.copyfile(__file__,O/'freeze.py');files=[{'path':str(f.relative_to(R)),'sha256':sha(f),'bytes':f.stat().st_size} for f in sorted(O.rglob('*')) if f.is_file()];(O/'FILES.json').write_text(json.dumps(files,indent=2)+'\n');print(json.dumps({'status':'PASS','files':len(files),'manifest_sha256':sha(O/'FILES.json')},indent=2))
