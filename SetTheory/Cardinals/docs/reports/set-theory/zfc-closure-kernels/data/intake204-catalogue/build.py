from pathlib import Path
import subprocess,time,json,hashlib,shutil
repo=Path('/home/codex/.codex/worktrees/ec20/Proofs');src=repo/'SetTheory/Cardinals/docs/reports/manifest.tex';out=Path('/tmp/zfc-intake204-catalogue/build');out.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
original=repo/'SetTheory/Cardinals/docs/reports/manifest.pdf';shutil.copyfile(original,out/'previous-manifest.pdf');shutil.copyfile(src,out/'source.tex');sourcehash=sha(src)
version=subprocess.check_output(['pdflatex','--version'],text=True);(out/'toolchain.txt').write_text(version)
records=[]
for i in [1,2]:
 cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error','-file-line-error','-no-shell-escape','-output-directory',str(out),str(src)]
 start=time.monotonic()
 with (out/f'pass{i}.stdout').open('wb') as f:
  result=subprocess.run(cmd,cwd=src.parent,stdout=f,stderr=subprocess.STDOUT,timeout=120)
 record={'pass':i,'argv':cmd,'cwd':str(src.parent),'exit_code':result.returncode,'seconds':time.monotonic()-start,'stdout_sha256':sha(out/f'pass{i}.stdout')}
 records.append(record)
 (out/f'pass{i}.log').write_bytes((out/'manifest.log').read_bytes())
 if result.returncode:break
assert sha(src)==sourcehash
res={'source':str(src.relative_to(repo)),'source_sha256':sourcehash,'toolchain':version.splitlines()[0],'jobs':records,'source_unchanged':True,'status':'PASS' if len(records)==2 and all(x['exit_code']==0 for x in records) else 'FAIL'}
if (out/'manifest.pdf').exists():res['pdf_sha256']=sha(out/'manifest.pdf')
(out/'result.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
