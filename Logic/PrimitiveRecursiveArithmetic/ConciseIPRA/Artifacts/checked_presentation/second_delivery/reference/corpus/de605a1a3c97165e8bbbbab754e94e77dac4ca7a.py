"""Build report.pdf using installed TeX, with a local-format fallback.

No downloads or system configuration changes are performed. The fallback
only addresses installations that have TeX sources but no generated format
or font map. All generated support files stay in a temporary directory.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def locate(name):
    r = subprocess.run(['kpsewhich', name], text=True, capture_output=True)
    return r.stdout.strip() if r.returncode == 0 else ''


def main():
    with tempfile.TemporaryDirectory(prefix='ipra-tex-') as folder:
        temp = Path(folder)
        env = os.environ.copy()
        if not locate('pdflatex.fmt'):
            subprocess.run(['pdftex', '-ini', '-etex', '-jobname=pdflatex',
                            '-progname=pdflatex', 'pdflatex.ini'], cwd=temp,
                           env=env, check=True)
            env['TEXFORMATS'] = str(temp) + os.pathsep + env.get('TEXFORMATS', '')
        if not locate('pdftex.map'):
            paths = [locate(name) for name in
                     ['lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']]
            if not all(paths):
                raise RuntimeError('Install Latin Modern and AMS Type 1 font maps.')
            (temp / 'pdftex.map').write_text('\n'.join(Path(p).read_text() for p in paths))
            env['TEXFONTMAPS'] = str(temp) + os.pathsep + env.get('TEXFONTMAPS', '')
        if shutil.which('latexmk'):
            commands = [['latexmk', '-g', '-pdf', '-interaction=nonstopmode',
                         '-halt-on-error', 'report.tex']]
        else:
            commands = [['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                         'report.tex']] * 3
        for command in commands:
            subprocess.run(command, cwd=ROOT, env=env, check=True)
    print('Built', ROOT / 'report.pdf')


if __name__ == '__main__':
    main()
