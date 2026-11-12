"""Expand a standalone TeX source and compile it without shell escape."""
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def expand(text, active=()):
    def include(match):
        relative = match.group(1)
        if relative in active:
            raise ValueError('Cyclic TeX input: ' + relative)
        return expand((ROOT / relative).read_text(), active + (relative,))
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def code(match):
        options, relative = match.group(1) or '', match.group(2)
        return '\\begin{lstlisting}' + options + '\n' + (ROOT / relative).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', code, text)


def main():
    (ROOT / 'report.tex').write_text(expand((ROOT / 'report_main.tex').read_text()))
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    for _ in range(3):
        result = subprocess.run(['pdflatex', '-no-shell-escape', '-halt-on-error',
                                 '-interaction=nonstopmode', '-output-directory', str(build),
                                 str(ROOT / 'report.tex')], cwd=ROOT,
                                capture_output=True, text=True)
        (build / 'build_stdout.txt').write_text(result.stdout + result.stderr)
        if result.returncode:
            raise SystemExit(result.stdout[-6000:] + result.stderr)
    shutil.copyfile(build / 'report.pdf', ROOT / 'report.pdf')
    print(str(ROOT / 'report.pdf'))


if __name__ == '__main__':
    main()
