"""Assemble the standalone LaTeX source from editable local sections."""
from pathlib import Path


def main():
    root = Path(__file__).resolve().parent
    middle = (root / 'ur_complete.tex').read_text()
    for name in ('ur_retraction.tex', 'ur_predecessor.tex', 'ur_reflection.tex'):
        middle = middle.replace('\\input{' + name + '}', (root / name).read_text())
    source = (root / 'report_front.tex').read_text() + '\n' + middle + '\n'
    source += (root / 'report_back.tex').read_text()
    if '\\input{' in source or '\\lstinputlisting' in source:
        raise RuntimeError('The delivered report source must be standalone')
    (root / 'report.tex').write_text(source)


if __name__ == '__main__':
    main()
