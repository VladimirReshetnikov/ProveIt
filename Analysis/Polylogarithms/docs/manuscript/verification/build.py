"""Three serial LuaLaTeX passes and a separately recorded convergence check."""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess
B=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--output-directory',type=Path,default=B)
args=parser.parse_args()
output=args.output_directory.resolve()
output.mkdir(parents=True,exist_ok=True)
passes=[]; previous=None
for n in range(1,4):
    proc=subprocess.run(['lualatex','-interaction=nonstopmode','-halt-on-error',f'-output-directory={output.as_posix()}','polylogarithms.tex'],
                        cwd=B,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8',errors='replace')
    (B/'verification'/f'latex-pass{n}.txt').write_text(proc.stdout,encoding='utf-8')
    state=hashlib.sha256(b''.join((output/('polylogarithms.'+s)).read_bytes() for s in ('aux','toc'))).hexdigest()
    passes.append(dict(pass_number=n,exit_code=proc.returncode,reference_state_sha256=state))
    print('LuaLaTeX pass',n,'exit',proc.returncode,flush=True)
    if proc.returncode:raise SystemExit(proc.returncode)
    if n==3:converged=previous==state
    previous=state
log=(output/'polylogarithms.log').read_text(encoding='utf-8',errors='replace')
issues=[line for line in log.splitlines() if any(x in line for x in ('undefined','multiply defined','Overfull','Missing character','Rerun to get','Label(s) may have changed'))]
pdf=B/'polylogarithms.pdf'
if output!=B:
    if not converged or issues:raise SystemExit('Isolated build failed convergence or log checks; canonical PDF preserved.')
    shutil.copyfile(output/'polylogarithms.pdf',pdf)
record=dict(passes=passes,converged=converged,final_issues=issues,pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),
            pdf_bytes=pdf.stat().st_size,passed=converged and not issues)
(B/'verification/build-results.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
raise SystemExit(0 if record['passed'] else 1)
