#!/usr/bin/env python3
"""Build the standalone article in a temporary directory and check the TeX log."""
from pathlib import Path
import json,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parent

def main():
    engine=shutil.which('pdflatex')
    if engine is None:raise SystemExit('pdflatex was not found. Install a TeX distribution and retry.')
    with tempfile.TemporaryDirectory(prefix='proveit_mixed_tails_') as tmp:
        work=Path(tmp);shutil.copy2(ROOT/'article.tex',work/'article.tex')
        for _ in range(3):
            run=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','article.tex'],cwd=work,text=True,capture_output=True)
            if run.returncode:
                (ROOT/'results'/'build_failure.log').write_text(run.stdout+run.stderr)
                raise SystemExit('TeX build failed; see results/build_failure.log.')
        log=(work/'article.log').read_text(errors='replace')
        (ROOT/'results'/'build.log').write_text(log)
        issues=[word for word in ('Overfull \\hbox','Overfull \\vbox','undefined references','Citation `','Reference `') if word in log]
        if issues:raise SystemExit('Build review required: '+', '.join(issues))
        shutil.copy2(work/'article.pdf',ROOT/'article.pdf')
    version=subprocess.run([engine,'--version'],text=True,capture_output=True).stdout.splitlines()[0]
    receipt={'status':'passed','passes':3,'engine':version,'overfull_boxes':0,'unresolved_references':0,'source':'article.tex','output':'article.pdf'}
    (ROOT/'results'/'build.json').write_text(json.dumps(receipt,indent=2))
    print('Built article.pdf with no overfull boxes or unresolved references.')
if __name__=='__main__':main()
