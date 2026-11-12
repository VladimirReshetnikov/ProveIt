"""Flatten the TeX/code inputs and optionally compile the complete paper."""
import argparse
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_deterministic_auxiliary'


def flatten(text):
    def include(match):
        path = ROOT / match.group(1)
        if not path.suffix:
            path = path.with_suffix('.tex')
        return '\n% BEGIN INCLUDED ' + str(path.relative_to(ROOT)) + '\n' + flatten(path.read_text()) + '\n% END INCLUDED\n'
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        return '\\begin{lstlisting}\n' + (ROOT / match.group(1)).read_text().rstrip() + '\n\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting\{([^}]+)\}', listing, text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    args = parser.parse_args()
    target = ROOT / (NAME + '.tex')
    target.write_text(flatten((ROOT / 'paper.tex').read_text()))
    if not args.source_only:
        for _ in range(2):
            result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                     '-halt-on-error', target.name],
                                    cwd=ROOT, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout[-6000:])
                raise SystemExit(result.returncode)
        print(ROOT / (NAME + '.pdf'))
    else:
        print(target)


if __name__ == '__main__':
    main()
