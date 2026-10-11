"""Build the article and fail on LaTeX errors or unresolved references."""
from pathlib import Path
import shutil,subprocess,sys
root=Path(__file__).resolve().parent
engine=shutil.which('pdflatex')
if not engine:
    raise SystemExit('pdflatex was not found. Install a TeX distribution with the packages named in article.tex.')
for pass_number in range(1,4):
    result=subprocess.run([engine,'-interaction=nonstopmode','-halt-on-error','article.tex'],cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (root/f'build-pass-{pass_number}.txt').write_text(result.stdout)
    if result.returncode:
        print(result.stdout[-10000:]);raise SystemExit(result.returncode)
log=(root/'article.log').read_text(errors='replace')
if 'There were undefined references' in log or 'There were undefined citations' in log:
    raise SystemExit('Unresolved references or citations remain; inspect article.log')
print(root/'article.pdf')
