from pathlib import Path
import os,json,hashlib,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';P=Path('/tmp/current-hierarchy2011-author-betz9tp8');I=Path('/tmp/current-hierarchy2011-independent-mgapxmxb');F=Path('/tmp/current-hierarchy2011-independent-euj3x5p4');out=D/'reviews/arithmetic-current-hierarchy2011-replay';assert not out.exists();out.mkdir()
def put(src,dst):
 src=Path(src); dst=out/dst;dst.parent.mkdir(parents=True,exist_ok=True);assert src.is_file() and not dst.exists();os.link(src,dst)
s=json.loads((P/'AUTHOR.json').read_text());assert s['status']=='FAILED' and s['attempts'][-1]['failure']=='final HEAD' and all(r['status']=='PASS' for r in s['records']);assert json.loads((P/'postcheck.json').read_text())['status']=='PASS';assert json.loads((I/'result.json').read_text())['status']=='PASS'
for f in ['AUTHOR.json','postcheck.json']:put(P/f,'author/'+f)
for f in ['driver.py','inputs.json']:put(P/'attempts/001'/f,'author/'+f)
for row in s['records']:
 n=row['module']
 for k in ['snapshot','log','timing']:put(row[k]['path'],'author/records/'+n+'/'+k+Path(row[k]['path']).suffix)
for f in I.iterdir():
 if f.is_file():put(f,'independent-pass/'+f.name)
for f in F.iterdir():
 if f.is_file():put(f,'independent-failed/'+f.name)
shutil.copyfile('/tmp/current-hierarchy2011-postcheck.py',out/'postcheck.py');shutil.copyfile(__file__,out/'freeze.py')
files=[]
for f in sorted(out.rglob('*')):
 if f.is_file():
  b=f.read_bytes();files.append({'path':str(f.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(out/'FILES.json').write_text(json.dumps(files,indent=2)+'\n'); print('PASS',len(files),'files',flush=True)
