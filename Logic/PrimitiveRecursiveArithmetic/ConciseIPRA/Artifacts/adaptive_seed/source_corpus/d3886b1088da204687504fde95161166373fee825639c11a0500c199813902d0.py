"""Build the paper, including a self-contained expanded LaTeX source."""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent


def expand(path):
    source = path.read_text()
    pattern = re.compile(r'\\input\{([^}]+)\}')
    def replace(match):
        target = ROOT / match.group(1)
        if not target.suffix:
            target = target.with_suffix('.tex')
        return '\n% BEGIN ' + match.group(1) + '\n' + expand(target) + '\n% END ' + match.group(1) + '\n'
    return pattern.sub(replace, source)


def main():
    (ROOT / 'report_standalone.tex').write_text(expand(ROOT / 'report.tex'))
    for _ in range(3):
        result = subprocess.run(['pdflatex', '-no-shell-escape', '-halt-on-error',
                                 '-interaction=nonstopmode', 'report.tex'],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            print(result.stdout[-10000:])
            raise SystemExit(result.returncode)
    log = (ROOT / 'report.log').read_text()
    failures = [line for line in log.splitlines()
                if ('undefined' in line.lower() or 'Overfull' in line or 'multiply defined' in line)]
    if failures:
        raise RuntimeError('Unresolved document warnings:\n' + '\n'.join(failures))
    print('Built report.pdf and report_standalone.tex without unresolved references or overfull boxes.')


if __name__ == '__main__':
    main()
