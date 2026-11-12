"""Assemble a standalone TeX report from the maintained sections."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def expand(text):
    def include(match):
        return expand((ROOT / match.group(1)).read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        return '\\begin{lstlisting}\n' + (ROOT / match.group(1)).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting\{([^}]+)\}', listing, text)


(ROOT / 'report.tex').write_text(expand((ROOT / 'paper/main.tex').read_text()))
print('Assembled report.tex')
