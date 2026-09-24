#!/usr/bin/env python3
"""Build the standalone paper with three pdfLaTeX passes (no shell escape)."""
from pathlib import Path
import shutil
import subprocess
import sys

def main() -> None:
    root = Path(__file__).resolve().parent
    engine = shutil.which('pdflatex')
    if engine is None:
        raise SystemExit('pdflatex was not found. Install TeX Live or MiKTeX and retry.')
    for number in range(1, 4):
        print(f'pdfLaTeX pass {number}/3', flush=True)
        result = subprocess.run([engine, '-interaction=nonstopmode', '-halt-on-error',
                                 '-file-line-error', 'article.tex'], cwd=root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, errors='replace')
        (root / f'build-pass-{number}.txt').write_text(result.stdout, encoding='utf-8')
        if result.returncode:
            print(result.stdout[-12000:], file=sys.stderr)
            raise SystemExit(f'Build failed on pass {number}; see build-pass-{number}.txt.')
    print(f'Built {root / "article.pdf"}')

if __name__ == '__main__':
    main()
