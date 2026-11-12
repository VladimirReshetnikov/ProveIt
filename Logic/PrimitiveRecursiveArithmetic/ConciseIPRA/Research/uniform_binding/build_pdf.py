"""Compile the standalone report without shell escape."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def environment(temporary):
    env = os.environ.copy()
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    # Some minimal Debian images contain the complete TeX source tree but
    # omit the generated format, map database, and system configuration.
    # Build only a private temporary cache; never change the installation.
    dist = Path('/usr/share/texlive/texmf-dist')
    fonts = Path('/usr/share/texmf')
    if not (dist / 'tex/latex/base/latex.ltx').is_file():
        raise SystemExit('The installed TeX format is missing; configure TeX Live.')
    env.update(TEXMFCNF=str(dist / 'web2c'),
               TEXMF='{' + str(dist) + ',' + str(fonts) + '}',
               TEXMFVAR=str(temporary / 'texmf-var'),
               TEXMFCONFIG=str(temporary / 'texmf-config'),
               TEXFORMATS=str(temporary) + os.pathsep)
    maps = [fonts / 'fonts/map/dvips/lm/lm.map']
    maps += [dist / ('fonts/map/dvips/amsfonts/' + name)
             for name in ['cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map']]
    (temporary / 'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
    init = subprocess.run(['pdftex', '-ini', '-etex', '-jobname=pdflatex',
                           '-progname=pdflatex', '-interaction=nonstopmode',
                           '-halt-on-error', '-no-shell-escape', 'pdflatex.ini'],
                          cwd=temporary, env=env, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if init.returncode:
        print(init.stdout[-12000:])
        raise SystemExit(init.returncode)
    return env


def main():
    compiler = shutil.which('pdflatex')
    if compiler is None:
        raise SystemExit('Install pdfLaTeX and the packages listed in report.tex.')
    with tempfile.TemporaryDirectory(prefix='ipra-uniform-binding-') as temporary:
        temporary = Path(temporary)
        env = environment(temporary)
        shutil.copy2(ROOT / 'report.tex', temporary / 'report.tex')
        command = [compiler, '-interaction=nonstopmode', '-halt-on-error',
                   '-no-shell-escape', 'report.tex']
        for _ in range(2):
            result = subprocess.run(command, cwd=temporary, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout[-12000:])
                raise SystemExit(result.returncode)
        shutil.copy2(temporary / 'report.pdf', ROOT / 'report.pdf')
        (ROOT / 'evidence/latex_build.log').write_text(result.stdout)
    print('Built report.pdf')


if __name__ == '__main__':
    main()

