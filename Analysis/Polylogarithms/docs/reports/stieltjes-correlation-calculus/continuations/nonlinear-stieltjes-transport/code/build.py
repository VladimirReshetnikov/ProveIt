#!/usr/bin/env python3
"""Compile the standalone article in a temporary directory; preserve a receipt."""
import json,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
    exe=shutil.which('pdflatex')
    if not exe: raise SystemExit('pdflatex is required to build article.pdf.')
    started=time.time()
    with tempfile.TemporaryDirectory(prefix='nonlinear-stieltjes-') as tmp:
        tmp=Path(tmp); shutil.copy(ROOT/'article.tex',tmp/'article.tex'); (tmp/'data').mkdir()
        shutil.copy(ROOT/'data/validation_summary.tex',tmp/'data/validation_summary.tex')
        outputs=[]
        for i in range(3):
            p=subprocess.run([exe,'-interaction=nonstopmode','-halt-on-error','article.tex'],cwd=tmp,capture_output=True,text=True)
            outputs.append(p.stdout)
            if p.returncode:
                (ROOT/'data/failed_build.log').write_text(p.stdout+p.stderr)
                raise SystemExit(f'LaTeX build failed on pass {i+1}; see data/failed_build.log')
        log=(tmp/'article.log').read_text()
        shutil.copy(tmp/'article.pdf',ROOT/'article.pdf')
        warnings=[line for line in log.splitlines() if any(s in line for s in ['Overfull','undefined','LaTeX Warning'])]
        receipt={'passed':True,'passes':3,'engine':subprocess.check_output([exe,'--version'],text=True).splitlines()[0],'elapsed_seconds':round(time.time()-started,3),'warnings':warnings}
        (ROOT/'data/build_receipt.json').write_text(json.dumps(receipt,indent=2))
        (ROOT/'data/latex_warnings.txt').write_text('\n'.join(warnings)+'\n')
        print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
