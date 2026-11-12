#!/usr/bin/env python3
"""Assemble a standalone TeX report; optionally compile with pdflatex."""
from pathlib import Path
import argparse
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FOUNDATIONS = [
    'inherited_choice_basis.tex',
    'inherited_ordinary_bridge.tex',
    'scalar_predecessor.tex',
    'equality_reflection.tex',
    'primitive_recursion.tex',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    pieces = [(ROOT / 'paper' / 'main_body.tex').read_text()]
    for name in FOUNDATIONS:
        pieces.append('% BEGIN INHERITED SOURCE: ' + name + '\n')
        pieces.append((ROOT / 'reference' / 'foundations' / name).read_text())
        pieces.append('% END INHERITED SOURCE: ' + name + '\n')
    ending = (ROOT / 'paper' / 'end.tex').read_text()
    listing = ('\\begin{lstlisting}\n' + (ROOT / 'code' / 'reduced.py').read_text()
               + '\\end{lstlisting}\n')
    ending = ending.replace('% The build script inserts the complete listing here.', listing)
    pieces.append(ending)
    target = ROOT / 'ipra_reduced_clause_calculus.tex'
    target.write_text('\n'.join(pieces), encoding='utf-8')
    print(target.name)
    if args.pdf:
        for _ in range(2):
            subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                            target.name], cwd=ROOT, check=True)


if __name__ == '__main__':
    main()
