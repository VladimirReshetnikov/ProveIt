"""Build the complete report without network access or shell escape."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent


def expand(path):
    text = path.read_text()
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda m: expand(ROOT / (m.group(1) if m.group(1).endswith('.tex') else m.group(1) + '.tex')),
                  text)
    def listing(match):
        options, filename = match.groups()
        return '\\begin{lstlisting}' + (options or '') + '\n' + (ROOT / filename).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


if __name__ == '__main__':
    (ROOT / 'ipra_neutral_scope.tex').write_text(expand(ROOT / 'report.tex'))
    for _ in range(3):
        result = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                 '-halt-on-error', 'ipra_neutral_scope.tex'], cwd=ROOT,
                                capture_output=True, text=True)
        if result.returncode:
            print(result.stdout[-12000:])
            raise SystemExit(result.returncode)
    log = (ROOT / 'ipra_neutral_scope.log').read_text()
    warnings = [line for line in log.splitlines() if
                'Overfull' in line or 'undefined' in line or 'multiply defined' in line]
    print('\n'.join(warnings) if warnings else 'PDF compiled: no overfull boxes or unresolved references.')
