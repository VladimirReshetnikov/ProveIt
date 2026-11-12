"""Build a standalone TeX source and its PDF using an installed TeX setup."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_counter_congruence'


def expand(text):
    def include(match):
        path = ROOT / match.group(1)
        return expand(path.read_text())
    return re.sub(r'\\input\{([^}]+)\}', include, text)


def main():
    (ROOT / (STEM + '.tex')).write_text(expand((ROOT / 'report.tex').read_text()))
    temporary = ROOT / 'tmp' / 'latex'
    temporary.mkdir(parents=True, exist_ok=True)
    logs = []
    for _ in range(3):
        result = subprocess.run(
            ['pdflatex', '-no-shell-escape', '-halt-on-error',
             '-interaction=nonstopmode', '-output-directory=' + str(temporary),
             STEM + '.tex'], cwd=ROOT, capture_output=True, text=True)
        logs.append(result.stdout + result.stderr)
        (ROOT / 'evidence' / 'latex_build.log').write_text('\n'.join(logs))
        if result.returncode:
            raise SystemExit(result.stdout[-6000:] + result.stderr)
    shutil.copyfile(temporary / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
    print(ROOT / (STEM + '.pdf'))


if __name__ == '__main__':
    main()
