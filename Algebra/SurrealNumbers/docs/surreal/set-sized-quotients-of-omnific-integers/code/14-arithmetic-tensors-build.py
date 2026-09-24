#!/usr/bin/env python3
"""Build article.pdf with three pdfLaTeX passes; Python 3.9+."""
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent
    engine = shutil.which('pdflatex')
    if engine is None:
        print('pdflatex is not on PATH. Install/configure a LaTeX distribution first.', file=sys.stderr)
        return 2
    for n in range(1, 4):
        print(f'pdfLaTeX pass {n}/3', flush=True)
        result = subprocess.run(
            [engine, '-interaction=nonstopmode', '-halt-on-error', 'article.tex'],
            cwd=str(root), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding='utf-8', errors='replace', check=False)
        (root / f'build-pass-{n}.log').write_text(result.stdout, encoding='utf-8')
        if result.returncode:
            print(result.stdout[-8000:], file=sys.stderr)
            return result.returncode
    pdf = root / 'article.pdf'
    if not pdf.is_file():
        print('The engine exited successfully but article.pdf is missing.', file=sys.stderr)
        return 3
    print(f'Built {pdf} ({pdf.stat().st_size:,} bytes)')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
