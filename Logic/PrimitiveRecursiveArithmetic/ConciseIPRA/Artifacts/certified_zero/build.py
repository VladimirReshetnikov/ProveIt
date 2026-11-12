"""Build the standalone LaTeX source and PDF in an isolated temporary directory."""
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_certified_zero'


def expand(path):
    content = path.read_text()
    content = re.sub(r'\\input\{([^}]+)\}',
                     lambda match: '\n% BEGIN ' + match[1] + '\n'
                     + expand(ROOT / match[1]) + '\n% END ' + match[1] + '\n', content)
    content = re.sub(r'\\lstinputlisting(?:\[([^]]*)\])?\{([^}]+)\}',
                     lambda match: '\\begin{lstlisting}'
                     + ('[' + match[1] + ']' if match[1] else '') + '\n'
                     + (ROOT / match[2]).read_text() + '\\end{lstlisting}', content)
    return content


def main():
    source = expand(ROOT / 'report_main.tex')
    (ROOT / (STEM + '.tex')).write_text(source)
    with tempfile.TemporaryDirectory(prefix='ipra_latex_') as directory:
        temporary = Path(directory)
        (temporary / (STEM + '.tex')).write_text(source)
        environment = dict(os.environ)
        environment['SOURCE_DATE_EPOCH'] = '1794333600'
        logs = []
        for _ in range(3):
            run = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                  '-halt-on-error', STEM + '.tex'],
                                 cwd=temporary, env=environment,
                                 text=True, capture_output=True)
            logs.append(run.stdout)
            if run.returncode:
                raise RuntimeError(run.stdout[-8000:] + run.stderr)
        shutil.copyfile(temporary / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
        (ROOT / 'evidence/latex_build.log').write_text((temporary / (STEM + '.log')).read_text())
    print('Built', STEM + '.tex', 'and', STEM + '.pdf')


if __name__ == '__main__':
    main()
