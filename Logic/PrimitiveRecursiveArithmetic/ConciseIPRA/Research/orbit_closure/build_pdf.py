"""Build the self-contained TeX report with pdflatex, without shell escape."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
with tempfile.TemporaryDirectory(prefix='ipra-orbit-tex-') as directory:
    build = Path(directory)
    shutil.copy2(ROOT / 'report.tex', build / 'report.tex')
    outputs = []
    environment = os.environ.copy()
    available = subprocess.run(['kpsewhich', 'pdflatex.fmt'], text=True,
                               capture_output=True, timeout=15)
    if not available.stdout.strip():
        initialized = subprocess.run(
            ['pdftex', '-ini', '-interaction=nonstopmode', '-halt-on-error',
             '-jobname=pdflatex', '-progname=pdflatex', '*pdflatex.ini'],
            cwd=build, text=True, capture_output=True, timeout=60)
        outputs.append(initialized.stdout + initialized.stderr)
        if initialized.returncode:
            raise RuntimeError(outputs[-1])
        environment['TEXFORMATS'] = str(build) + os.pathsep + environment.get('TEXFORMATS', '')
    for _ in range(3):
        result = subprocess.run(
            ['pdflatex', '-no-shell-escape', '-halt-on-error', '-interaction=nonstopmode', 'report.tex'],
            cwd=build, env=environment, text=True, capture_output=True, timeout=60)
        outputs.append(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(outputs[-1])
    shutil.copy2(build / 'report.pdf', ROOT / 'report.pdf')
    (ROOT / 'evidence').mkdir(exist_ok=True)
    (ROOT / 'evidence/pdf_build.txt').write_text('\n'.join(outputs))
    (ROOT / 'evidence/latex_final.log').write_text((build / 'report.log').read_text())
print(ROOT / 'report.pdf')
