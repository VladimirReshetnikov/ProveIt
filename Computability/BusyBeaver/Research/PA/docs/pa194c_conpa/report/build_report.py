#!/usr/bin/env python3
"""Build the report using installed TeX Live; no network or extra Python packages."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def locate(name):
    result = subprocess.run(['kpsewhich', name], text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else ''


def main():
    if not shutil.which('pdflatex') or not shutil.which('kpsewhich'):
        raise SystemExit('Install TeX Live with the packages listed in the report preamble.')
    with tempfile.TemporaryDirectory(prefix='pa194c-tex-') as temp:
        env = os.environ.copy()
        command = ['pdflatex']
        if not locate('pdflatex.fmt'):
            subprocess.run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                            '-halt-on-error', '-jobname=pdflatex',
                            '-output-directory=' + temp, 'pdflatex.ini'],
                           cwd=HERE, env=env, check=True)
            command.append('-fmt=' + str(Path(temp) / 'pdflatex.fmt'))
        if not locate('pdftex.map'):
            maps = []
            for name in ['lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']:
                path = locate(name)
                if path:
                    maps.append(Path(path).read_text())
            if not maps:
                raise SystemExit('No installed scalable-font maps found.')
            (Path(temp) / 'pdftex.map').write_text('\n'.join(maps))
            env['TEXFONTMAPS'] = temp + os.pathsep + env.get('TEXFONTMAPS', '')
        command += ['-interaction=nonstopmode', '-halt-on-error', 'pa194c_conpa.tex']
        for _ in range(3):
            subprocess.run(command, cwd=HERE, env=env, check=True)
    print(HERE / 'pa194c_conpa.pdf')


if __name__ == '__main__':
    main()
