from pathlib import Path
import hashlib,json,os,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');O=R/'Computability/DiophantineConsistency/reviews/adaptive-factor-magnitude2011-build-evidence';assert not O.exists();O.mkdir()
roots=['/tmp/adaptive13-factor-ct2mhn26','/tmp/adaptive13-factor-o2f4p8_a','/tmp/adaptive13-factor-ccn656uq','/tmp/adaptive13-factor-77nbda71']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for i,x in enumerate(roots,1):
 p=Path(x);q=O/('attempt-%02d'%i);q.mkdir();state=json.loads((p/'state.json').read_text());assert state['status'] in ['PASS','FAILED']
 for f in [p/'state.json',p/'providers.json',p/'driver.py',*sorted((p/'logs').iterdir())]:
  assert f.is_file() and not f.is_symlink();os.link(f,q/f.name)
shutil.copyfile('/tmp/adaptive13-factor-driver-preflight-failure.py',O/'preflight-failure.py');shutil.copyfile(__file__,O/'freeze.py')
a=json.loads((O/'attempt-03/state.json').read_text());b=json.loads((O/'attempt-04/state.json').read_text());assert a['status']==b['status']=='PASS'
for x,y in zip(a['records'],b['records'],strict=True):assert all(x[k]==y[k] for k in ['name','source_sha256','object_sha256','log_sha256'])
files=[{'path':str(f.relative_to(R)),'sha256':sha(f),'bytes':f.stat().st_size} for f in sorted(O.rglob('*')) if f.is_file()];(O/'FILES.json').write_text(json.dumps(files,indent=2)+'\n');print(json.dumps({'status':'PASS','files':len(files),'manifest_sha256':sha(O/'FILES.json')},indent=2))
