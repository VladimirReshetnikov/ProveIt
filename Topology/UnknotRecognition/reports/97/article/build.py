#!/usr/bin/env python3
"""Compile the complete article using an installed TeX distribution."""

from pathlib import Path
import shutil
import subprocess


def main():
    directory = Path(__file__).resolve().parent
    if shutil.which('latexmk'):
        subprocess.run(['latexmk', '-pdf', '-interaction=nonstopmode',
                        '-halt-on-error', 'Stopping_Cores.tex'],
                       cwd=directory, check=True)
    elif shutil.which('pdflatex'):
        for _ in range(3):
            subprocess.run(['pdflatex', '-interaction=nonstopmode',
                            '-halt-on-error', 'Stopping_Cores.tex'],
                           cwd=directory, check=True)
    else:
        raise SystemExit('Install a TeX distribution with pdflatex (and preferably latexmk).')
    print(directory / 'Stopping_Cores.pdf')


if __name__ == '__main__':
    main()
