"""Build a self-contained TeX source and compile it with shell escape disabled."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_coverage_and_kernel'


def expand(text):
    def include(match):
        path = ROOT / match.group(1)
        if not path.suffix:
            path = path.with_suffix('.tex')
        return expand(path.read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        return ('\\begin{lstlisting}' + (match.group(1) or '') + '\n' +
                (ROOT / match.group(2)).read_text().rstrip() +
                '\n\\end{lstlisting}')
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    source = expand((ROOT / 'report.tex').read_text())
    (ROOT / (STEM + '.tex')).write_text(source)
    build = ROOT / 'tmp' / 'latex'
    build.mkdir(parents=True, exist_ok=True)
    logs = []
    for _ in range(3):
        result = subprocess.run([
            'pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
            '-halt-on-error', '-file-line-error', '-output-directory=' + str(build),
            STEM + '.tex'], cwd=ROOT, capture_output=True, text=True)
        logs.append(result.stdout + result.stderr)
        if result.returncode:
            print((result.stdout + result.stderr)[-12000:])
            raise SystemExit(result.returncode)
    log = (build / (STEM + '.log')).read_text()
    (ROOT / 'evidence/latex_build.log').write_text('\n'.join(logs))
    (ROOT / 'evidence/latex_warnings.txt').write_text('\n'.join(
        line for line in log.splitlines() if
        'undefined' in line.lower() or 'Overfull' in line or
        'multiply defined' in line) + '\n')
    shutil.copyfile(build / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
    print(ROOT / (STEM + '.pdf'))


if __name__ == '__main__':
    main()
