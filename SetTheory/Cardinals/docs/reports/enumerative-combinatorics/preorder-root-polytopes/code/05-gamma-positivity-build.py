#!/usr/bin/env python3
"""Build article.tex with pdfLaTeX, preserving logs under build/."""
from __future__ import annotations
import shutil
import subprocess
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent
    engine = shutil.which('pdflatex')
    if engine is None:
        raise SystemExit('pdflatex was not found. Install a TeX distribution first.')
    out = root / 'build'
    out.mkdir(exist_ok=True)
    for number in range(1, 4):
        command = [engine, '-interaction=nonstopmode', '-halt-on-error',
                   '-output-directory', str(out), str(root / 'article.tex')]
        result = subprocess.run(command, cwd=root, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                check=False)
        log = out / f'compile-pass-{number}.log'
        log.write_text(result.stdout, encoding='utf-8')
        if result.returncode:
            raise SystemExit(f'LaTeX pass {number} failed; inspect {log}')
    pdf = out / 'article.pdf'
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise SystemExit('LaTeX returned without producing a usable PDF.')
    shutil.copy2(pdf, root / 'article.pdf')
    print(f'Built {root / "article.pdf"}')


if __name__ == '__main__':
    main()
