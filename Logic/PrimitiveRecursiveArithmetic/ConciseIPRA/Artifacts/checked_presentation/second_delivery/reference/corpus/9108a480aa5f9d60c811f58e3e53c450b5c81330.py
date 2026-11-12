"""Compile the included report using installed TeX, without downloads.

For source-only TeX installations, generate the missing format/font map in
a private temporary directory under the invoking working directory. TeX
caches are redirected there; system configuration is never modified.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def query(argument, env):
    result = subprocess.run(['kpsewhich', argument], env=env,
                            text=True, capture_output=True)
    return result.stdout.strip() if result.returncode == 0 else ''


def main():
    if not shutil.which('pdflatex') or not shutil.which('kpsewhich'):
        raise RuntimeError('Install TeX Live with pdfLaTeX and Latin Modern fonts.')
    with tempfile.TemporaryDirectory(prefix='ipra_tex_', dir=Path.cwd()) as folder:
        temporary = Path(folder)
        env = os.environ.copy()
        for variable in ('TEXMFVAR', 'TEXMFCONFIG', 'TEXMFCACHE'):
            target = temporary / variable.lower()
            target.mkdir()
            env[variable] = str(target)
        # Some source-only images retain database-only paths but omit ls-R.
        # Permit ordinary filesystem search for this build process only.
        if not query('pdflatex.ini', env):
            roots = query('-var-value=TEXMF', env)
            if roots:
                env['TEXMF'] = roots.replace('!!', '')
        if not query('pdflatex.fmt', env):
            if not query('pdflatex.ini', env):
                raise RuntimeError('The installed TeX distribution lacks pdflatex.ini.')
            subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                            '-interaction=nonstopmode', '-halt-on-error',
                            '-jobname=pdflatex', '-progname=pdflatex',
                            'pdflatex.ini'], cwd=temporary, env=env, check=True)
            env['TEXFORMATS'] = str(temporary) + os.pathsep + env.get('TEXFORMATS', '')
        if not query('pdftex.map', env):
            maps = [query(name, env) for name in
                    ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map')]
            if not all(maps):
                raise RuntimeError('The installed TeX distribution lacks required Type 1 font maps.')
            (temporary / 'pdftex.map').write_text('\n'.join(Path(p).read_text() for p in maps))
            env['TEXFONTMAPS'] = str(temporary) + os.pathsep + env.get('TEXFONTMAPS', '')
        command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                   '-file-line-error', '-no-shell-escape', 'report.tex']
        for _ in range(3):
            subprocess.run(command, cwd=ROOT, env=env, check=True)
    print('Built', ROOT / 'report.pdf')


if __name__ == '__main__':
    main()
