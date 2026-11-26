#!/usr/bin/env python3
"""Compile the standard LaTeX report; support a source-only TeX Live install.

The temporary-format fallback is used only when kpsewhich cannot locate
pdflatex.fmt. It does not modify the installed TeX distribution.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile


def call(command, base, env):
    print('Running:', ' '.join(map(str, command)), flush=True)
    subprocess.run(command, cwd=base, env=env, check=True)


def main():
    base = Path(__file__).resolve().parents[1]
    env = os.environ.copy()
    if not shutil.which('latexmk'):
        if shutil.which('tectonic'):
            call(['tectonic', 'report.tex', '--keep-logs'], base, env)
            return
        raise SystemExit('Install a complete TeX Live with latexmk or Tectonic.')
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True,
                           text=True, env=env)
    with tempfile.TemporaryDirectory(prefix='grh_report_tex_') as temp:
        runtime = Path(temp)
        if not probe.stdout.strip():
            roots = [p for p in (Path('/usr/share/texlive/texmf-dist'),
                                Path('/usr/share/texmf')) if p.exists()]
            if not roots:
                raise SystemExit('TeX Live is incomplete: install its LaTeX formats.')
            env['TEXINPUTS'] = '.:'+':'.join(str(p/'tex')+'//' for p in roots)+':'
            env['TEXFORMATS'] = str(runtime)+'//:'
            for name, subdir in [('TFMFONTS', 'tfm'), ('T1FONTS', 'type1'),
                                 ('VFFONTS', 'vf'), ('ENCFONTS', 'enc')]:
                env[name] = ':'.join(str(p/'fonts'/subdir)+'//' for p in roots)+':'
            env['TEXFONTMAPS'] = str(runtime)+'//:'+':'.join(
                str(p/'fonts/map')+'//' for p in roots)+':'
            maps = []
            for root in roots:
                lm = root/'fonts/map/dvips/lm/lm.map'
                if lm.exists():
                    maps.append(lm)
                maps.extend(sorted((root/'fonts/map/dvips/amsfonts').glob('*.map')))
            (runtime/'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
            call(['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                  '-halt-on-error', '-jobname=pdflatex', '*pdflatex.ini'], runtime, env)
        call(['latexmk', '-pdf', '-g', '-interaction=nonstopmode',
              '-halt-on-error', 'report.tex'], base, env)


if __name__ == '__main__':
    main()
