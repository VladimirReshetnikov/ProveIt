#!/usr/bin/env python3
"""Rebuild Report148 with a clean, deterministic, local TeX environment."""
import argparse
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True, help='new directory; existing targets and symlink parents are refused')
    args = parser.parse_args()
    raw = Path(args.output_dir)
    if '..' in raw.parts:
        raise ValueError('parent traversal is refused')
    out = Path(os.path.abspath(raw))
    for parent in [out] + list(out.parents):
        if parent.is_symlink():
            raise ValueError('symlink output paths are refused')
    if out.exists():
        raise FileExistsError('output directory must not exist')
    if not out.parent.is_dir():
        raise FileNotFoundError('output parent must already exist')
    root = Path(__file__).resolve().parent
    source = root / 'Report148.tex'
    if source.is_symlink() or not source.is_file():
        raise ValueError('expected regular Report148.tex beside this script')
    out.mkdir(mode=0o700)
    shutil.copyfile(source, out / source.name)
    env = {key: value for key, value in os.environ.items() if key in ('PATH', 'SYSTEMROOT', 'WINDIR')}
    env.update(SOURCE_DATE_EPOCH='1790985600', FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
    for key, name in [('HOME','home'),('TEXMFHOME','texmf-home'),('TEXMFVAR','texmf-var'),('TEXMFCONFIG','texmf-config'),('TEXMFCACHE','texmf-cache'),('XDG_CACHE_HOME','xdg-cache')]:
        folder = out / name
        folder.mkdir()
        env[key] = str(folder)
    env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXFORMATS'] = str(out) + '//:'
    fmt = ['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini']
    command = ['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',r'\pdfmapfile{}\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report148.tex}']
    with (out / 'build_console.txt').open('x', encoding='utf-8') as log:
        subprocess.run(fmt, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        previous_aux = None
        for run in range(5):
            subprocess.run(command, cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
            current_aux = (out / 'Report148.aux').read_bytes()
            if run >= 1 and current_aux == previous_aux:
                break
            previous_aux = current_aux
        else:
            raise RuntimeError('cross-references did not stabilize in five passes')
    tex_log = (out / 'Report148.log').read_text(encoding='utf-8', errors='replace')
    if re.search(r'\bwarning(?=[:\s(])|overfull|underfull|missing character:', tex_log, re.IGNORECASE):
        raise RuntimeError('TeX warning or box defect remains; inspect Report148.log')
    pdf = out / 'Report148.pdf'
    if not pdf.is_file() or pdf.stat().st_size == 0:
        raise RuntimeError('PDF missing after successful TeX build')
    print('Built Report148.pdf')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print('Build failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
