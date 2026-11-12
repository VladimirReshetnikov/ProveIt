"""Assemble the standalone LaTeX report from the editable sources."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def build():
    text = (ROOT / 'paper/manuscript.tex').read_text()
    fragments = [
        ('CHOICE', 'inherited_choice_basis.tex', 'app:choice'),
        ('ORDINARY', 'inherited_ordinary_bridge.tex', 'app:ordinary'),
        ('PREDECESSOR', 'scalar_predecessor.tex', 'app:pred'),
        ('EQUALITY', 'equality_reflection.tex', 'app:eq'),
        ('RECURSION', 'primitive_recursion.tex', 'app:pr'),
    ]
    for marker, filename, label in fragments:
        content = (ROOT / 'reference/bridge' / filename).read_text()
        first = content.index('\\section{')
        end = content.index('\n', first)
        content = content[:end] + '\n\\label{' + label + '}' + content[end:]
        text = text.replace('% APPENDIX_' + marker, content.rstrip())
    for marker, filename in [('RAW', 'raw_two_case.py'), ('CANONICAL', 'zero_base.py')]:
        listing = '\\begin{lstlisting}[language=Python]\n'
        listing += (ROOT / 'code' / filename).read_text().rstrip() + '\n'
        listing += '\\end{lstlisting}'
        text = text.replace('% LISTING_' + marker, listing)
    if '% APPENDIX_' in text or '% LISTING_' in text:
        raise RuntimeError('Unresolved assembly marker')
    (ROOT / 'report.tex').write_text(text)
    print('Assembled report.tex with all appendices and code listings embedded.')


if __name__ == '__main__':
    build()
