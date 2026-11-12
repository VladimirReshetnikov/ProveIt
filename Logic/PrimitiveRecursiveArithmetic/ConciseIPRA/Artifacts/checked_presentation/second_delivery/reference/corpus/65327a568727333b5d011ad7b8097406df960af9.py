"""Assemble one standalone LaTeX file from the editable sections."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PARTS = ['front.tex', 'arithmetic_begin.tex', 'logic.tex', 'arithmetic_end.tex', 'back.tex']


def main():
    text = '\n\n'.join((ROOT / 'paper' / name).read_text() for name in PARTS)
    text += '\n\\begin{lstlisting}[language=Python]\n'
    text += (ROOT / 'code/checker.py').read_text()
    text += '\n\\end{lstlisting}\n\\end{document}\n'
    (ROOT / 'report.tex').write_text(text)
    print('Assembled report.tex')


if __name__ == '__main__':
    main()

