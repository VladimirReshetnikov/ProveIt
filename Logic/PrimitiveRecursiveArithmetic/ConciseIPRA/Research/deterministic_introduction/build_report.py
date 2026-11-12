"""Build the standalone LaTeX report and compile it without shell escape."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def build():
    parts = ['preamble.tex', 'deterministic_introduction.tex', 'bridge.tex',
             'implementation.tex']
    text = '\n'.join((ROOT / name).read_text() for name in parts)
    text += '\n\\clearpage\n\\section{Complete checker for the new calculus}\n'
    text += ('This is the complete measured acceptance module after removal of '
             'its module docstring and normalization by \\texttt{ast.unparse}. '
             'It imports no proof-producing or verification helper.\n')
    text += '\\begin{lstlisting}\n'
    text += (ROOT / 'code/checker.normalized.py').read_text()
    text += '\\end{lstlisting}\n'
    text += (ROOT / 'references.tex').read_text()
    (ROOT / 'ipra_deterministic_introduction.tex').write_text(text)
    for _ in range(3):
        subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                        '-halt-on-error', 'ipra_deterministic_introduction.tex'],
                       cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    print('Built ipra_deterministic_introduction.pdf')


if __name__ == '__main__':
    build()
