"""Build the article with optional verification; no third-party Python packages."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true',
                        help='Run finite regression checks before building the PDF.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    if args.verify:
        subprocess.run([sys.executable, str(root/'code'/'verify.py')], cwd=root, check=True)
    latexmk = shutil.which('latexmk')
    pdflatex = shutil.which('pdflatex')
    if latexmk:
        commands = [[latexmk, '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                     'article.tex']]
    elif pdflatex:
        commands = [[pdflatex, '-interaction=nonstopmode', '-halt-on-error',
                     'article.tex']] * 3
    else:
        parser.error('A TeX installation with latexmk or pdflatex is required. '
                     'The supplied article.pdf can be read without rebuilding.')
    for command in commands:
        subprocess.run(command, cwd=root, check=True)
    print('Built:', root/'article.pdf')


if __name__ == '__main__':
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(f'Build stopped: command exited with status {error.returncode}.', file=sys.stderr)
        raise SystemExit(error.returncode)
