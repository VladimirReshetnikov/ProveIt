#!/usr/bin/env python3
"""Compile the supplied LaTeX report with an installed TeX distribution."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout[-12000:])
    return result.stdout


def main():
    latex = shutil.which('pdflatex')
    pdftex = shutil.which('pdftex')
    kpsewhich = shutil.which('kpsewhich')
    if not latex or not pdftex or not kpsewhich:
        raise SystemExit('Install TeX Live or another distribution providing pdflatex.')
    found = subprocess.run([kpsewhich, 'pdflatex.fmt'], cwd=ROOT,
                           text=True, capture_output=True).stdout.strip()
    with tempfile.TemporaryDirectory(prefix='ipra_tex_format_') as tmp:
        flags = []
        if not found:
            run([pdftex, '-ini', '-interaction=nonstopmode', '-halt-on-error',
                 '-jobname=pdflatex', '-progname=pdflatex', '-etex', 'pdflatex.ini'], tmp)
            flags = ['-fmt=' + str(Path(tmp) / 'pdflatex.fmt')]
        for _ in range(3):
            log = run([latex, *flags, '-interaction=nonstopmode', '-halt-on-error',
                       'ipra_frontier_review.tex'], ROOT)
        (ROOT / 'evidence/latex_build.txt').write_text(log)
    print(ROOT / 'ipra_frontier_review.pdf')


if __name__ == '__main__':
    main()
