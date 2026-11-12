"""Build the standalone report with pdfLaTeX, with shell escape disabled."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    source = ROOT / 'ipra_first_instance.tex'
    with tempfile.TemporaryDirectory(prefix='ipra-pdf-') as temporary:
        directory = Path(temporary)
        shutil.copyfile(source, directory / source.name)
        environment = os.environ.copy()
        def locate(name):
            result = subprocess.run(['kpsewhich', name], capture_output=True,
                                    text=True, env=environment)
            return result.stdout.strip()
        if not locate('pdflatex.fmt'):
            result = subprocess.run(
                ['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                 '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'],
                cwd=directory, capture_output=True, text=True, env=environment)
            if result.returncode:
                print(result.stdout[-12000:])
                raise SystemExit(result.returncode)
            environment['TEXFORMATS'] = str(directory) + os.pathsep
        if not locate('pdftex.map'):
            names = ['lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']
            maps = [locate(name) for name in names]
            if not all(maps):
                raise SystemExit('Install the Latin Modern and AMS font maps.')
            (directory / 'pdftex.map').write_text(
                '\n'.join(Path(path).read_text() for path in maps))
            environment['TEXFONTMAPS'] = str(directory) + os.pathsep
        for _ in range(3):
            result = subprocess.run(
                ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', source.name], cwd=directory,
                capture_output=True, text=True, env=environment)
            if result.returncode:
                print(result.stdout[-12000:])
                raise SystemExit(result.returncode)
        log = (directory / 'ipra_first_instance.log').read_text()
        (ROOT / 'evidence/pdf_build.log').write_text(log)
        shutil.copyfile(directory / 'ipra_first_instance.pdf',
                        ROOT / 'ipra_first_instance.pdf')
    print('Built ipra_first_instance.pdf')


if __name__ == '__main__':
    main()
