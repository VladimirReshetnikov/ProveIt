#!/usr/bin/env python3
"""Build the report without network access.

Uses ordinary pdflatex when configured. A local TeX Live fallback supports
an installation with existing packages but absent generated format/maps.
All generated TeX state is local to .build/; no system files are changed.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess


def run(cmd, cwd, env, log):
    with log.open('w') as f:
        p = subprocess.run(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    if p.returncode:
        tail = '\n'.join(log.read_text(errors='replace').splitlines()[-35:])
        raise RuntimeError(f'{cmd[0]} failed; see {log}\n{tail}')


def main():
    base = Path(__file__).resolve().parents[1]
    build = base / '.build'
    build.mkdir(exist_ok=True)
    env = os.environ.copy()
    pdflatex = shutil.which('pdflatex')
    if not pdflatex:
        raise RuntimeError('pdflatex is required; this script does not download software.')
    k = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, text=True)
    fallback = not (k.returncode == 0 and k.stdout.strip())
    if fallback:
        roots = [Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')]
        roots = [p for p in roots if p.is_dir()]
        if not roots:
            raise RuntimeError('No configured format or usable local TeX Live tree.')
        env['TEXMF'] = '{' + ','.join(map(str, roots)) + '}'
        runtime = build / 'tex-runtime'
        runtime.mkdir(exist_ok=True)
        maps = []
        for root in roots:
            for p in (root / 'fonts/map/dvips/amsfonts').glob('*.map'):
                maps.append(p)
            p = root / 'fonts/map/dvips/lm/lm.map'
            if p.is_file():
                maps.append(p)
        (runtime / 'pdftex.map').write_text('\n'.join(p.read_text(errors='ignore') for p in maps))
        env['TEXFORMATS'] = str(runtime) + os.pathsep
        env['TEXFONTMAPS'] = str(runtime) + '//' + os.pathsep
        if not (runtime / 'pdflatex.fmt').exists():
            run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode', '-halt-on-error',
                 '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                runtime, env, build / 'format-build.txt')
    for i in range(1, 4):
        run([pdflatex, '-interaction=nonstopmode', '-halt-on-error',
             '-output-directory=' + str(build), 'main.tex'],
            base / 'paper', env, build / f'latex-pass-{i}.txt')
    logfile = (build / 'main.log').read_text(errors='replace')
    unresolved = ('There were undefined references' in logfile or
                  'There were undefined citations' in logfile)
    if unresolved:
        raise RuntimeError('References remain unresolved after three passes.')
    output = base / 'ipra_certified_continuation.pdf'
    shutil.copyfile(build / 'main.pdf', output)
    verification = base / 'verification'
    verification.mkdir(exist_ok=True)
    warnings = [line for line in logfile.splitlines()
                if 'Overfull' in line or 'Warning:' in line]
    report = {'status': 'compiled', 'passes': 3, 'local_tex_fallback': fallback,
              'unresolved_references': unresolved, 'warnings': warnings,
              'pdf_bytes': output.stat().st_size}
    (verification / 'latex_build.json').write_text(json.dumps(report, indent=2) + '\n')
    (verification / 'latex_warnings.txt').write_text('\n'.join(warnings) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
