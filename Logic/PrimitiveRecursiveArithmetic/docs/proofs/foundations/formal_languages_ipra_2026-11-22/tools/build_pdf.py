#!/usr/bin/env python3
"""Build the LaTeX report, including in a TeX Live image with missing caches.

Usage (from the package directory):
    python3 tools/build_pdf.py formal_languages_ipra.tex --out-dir build

For ordinary TeX installations, use --system to invoke pdflatex normally.
The default Linux fallback creates only local format/font-map files. It does
not modify /etc, /var, /usr, HOME, or the installed TeX distribution. It requires
pdftex and the installed LaTeX/AMS/Latin Modern packages; it does not download
or install anything. English hyphenation is used for the locally built format.

The local helper addresses missing TeX Live filename databases and format
caches by using direct recursive search paths and a locally generated format.
"""
from __future__ import annotations
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys


def execute(command, *, cwd, env, log):
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.write_text(result.stdout)
    if result.returncode:
        print('\n'.join(result.stdout.splitlines()[-65:]), file=sys.stderr)
        raise SystemExit(f"TeX failed (exit {result.returncode}); see {log}")
    return result


def local_environment(runtime: Path):
    trees = [Path(p) for p in ('/usr/share/texlive/texmf-dist',
                              '/usr/share/texmf', '/etc/texmf') if Path(p).is_dir()]
    if not trees or not (trees[0] / 'tex/latex/base/latex.ltx').is_file():
        raise SystemExit('Expected Linux TeX Live tree missing; try --system.')
    runtime.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    # No !! prefix: search installed files directly instead of requiring ls-R.
    env['TEXMF'] = '{' + ','.join(map(str, trees)) + '}'
    texpaths = [str(p / 'tex') + '//' for p in trees if (p / 'tex').is_dir()]
    mappaths = [str(p / 'fonts/map') + '//' for p in trees if (p / 'fonts/map').is_dir()]
    env['TEXINPUTS'] = '.:' + str(runtime) + ':' + ':'.join(texpaths) + ':'
    env['TEXFORMATS'] = str(runtime) + ':'
    env['TEXFONTMAPS'] = str(runtime) + ':' + ':'.join(mappaths) + ':'
    # Avoid automated generation paths when a requested metric is truly absent.
    env['MKTEXPK'] = '0'
    env['MKTEXTFM'] = '0'
    (runtime / 'language.dat').write_text('english hyphen.tex\n')
    maps = []
    for tree in trees:
        ams = tree / 'fonts/map/dvips/amsfonts'
        if ams.is_dir():
            maps.extend(sorted(ams.glob('*.map')))
        for relative in ('fonts/map/dvips/lm/lm.map',
                         'fonts/map/dvips/helvetic/uhv.map',
                         'fonts/map/dvips/times/utm.map',
                         'fonts/map/dvips/courier/ucr.map'):
            path = tree / relative
            if path.is_file():
                maps.append(path)
    (runtime / 'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
    if not (runtime / 'pdflatex.fmt').is_file():
        binary = shutil.which('pdftex')
        if not binary:
            raise SystemExit('pdftex is unavailable.')
        execute([binary, '-ini', '-etex', '-jobname=pdflatex', '-progname=pdflatex',
                 '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'],
                cwd=runtime, env=env, log=runtime / 'format-build.stdout.log')
    return env


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tex', type=Path)
    parser.add_argument('--out-dir', type=Path, default=Path('build'))
    parser.add_argument('--runtime-dir', type=Path)
    parser.add_argument('--passes', type=int, default=3)
    parser.add_argument('--system', action='store_true',
                        help='Use the installed pdflatex format and configuration.')
    args = parser.parse_args()
    source = args.tex.resolve()
    if not source.is_file() or source.suffix.lower() != '.tex':
        raise SystemExit(f'No .tex source found: {source}')
    if args.passes < 1:
        raise SystemExit('--passes must be positive')
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if args.system:
        executable = shutil.which('pdflatex')
        if not executable:
            raise SystemExit('pdflatex is unavailable.')
        env = dict(os.environ)
        command = [executable]
    else:
        runtime = (args.runtime_dir or out / 'tex-runtime').resolve()
        env = local_environment(runtime)
        executable = shutil.which('pdftex')
        if not executable:
            raise SystemExit('pdftex is unavailable.')
        command = [executable, '-fmt=pdflatex', '-progname=pdflatex']
    command += ['-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                '-file-line-error', '-output-directory=' + str(out), source.name]
    for iteration in range(1, args.passes + 1):
        execute(command, cwd=source.parent, env=env,
                log=out / f'{source.stem}.pass-{iteration}.stdout.log')
        print(f'LaTeX pass {iteration}/{args.passes} completed.')
    pdf = out / (source.stem + '.pdf')
    if not pdf.is_file() or not pdf.read_bytes().startswith(b'%PDF-'):
        raise SystemExit('TeX exited successfully but did not create a PDF.')
    print(f'Created {pdf} ({pdf.stat().st_size:,} bytes).')


if __name__ == '__main__':
    main()
