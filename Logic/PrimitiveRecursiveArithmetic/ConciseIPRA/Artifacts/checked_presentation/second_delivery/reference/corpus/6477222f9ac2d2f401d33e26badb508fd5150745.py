"""Build the standalone LaTeX report without shell escape.

Requires TeX Live with the standard packages listed by the source.
If a distribution supplies TeX sources but no prebuilt pdflatex format,
this script builds that format locally in its temporary directory.
"""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_progress_independence'


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout[-16000:])
    return result.stdout


def main():
    with tempfile.TemporaryDirectory(prefix='ipra_pdf_') as directory:
        build = Path(directory)
        shutil.copyfile(ROOT / (STEM + '.tex'), build / (STEM + '.tex'))
        found = subprocess.run(['kpsewhich', 'pdflatex.fmt'],
                               stdout=subprocess.PIPE, text=True)
        extra = []
        if not found.stdout.strip():
            run(['pdftex', '-ini', '-etex', '-jobname=pdflatex',
                 '-progname=pdflatex', '-interaction=nonstopmode',
                 'pdflatex.ini'], build)
            extra = ['-fmt=' + str(build / 'pdflatex.fmt')]
        command = ['pdflatex'] + extra + ['-no-shell-escape',
                  '-interaction=nonstopmode', '-halt-on-error', STEM + '.tex']
        for _ in range(3):
            log = run(command, build)
        if 'Undefined control sequence' in log or 'There were undefined references' in log:
            raise RuntimeError('Unresolved TeX errors or references')
        shutil.copyfile(build / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
        (ROOT / 'evidence').mkdir(exist_ok=True)
        shutil.copyfile(build / (STEM + '.log'), ROOT / 'evidence/latex_build.log')
        print(ROOT / (STEM + '.pdf'))


if __name__ == '__main__':
    main()
