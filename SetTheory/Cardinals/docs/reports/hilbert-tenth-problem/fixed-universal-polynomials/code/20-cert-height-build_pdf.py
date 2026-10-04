#!/usr/bin/env python3
"""Deterministic local LaTeX build; no research code is executed."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
ROOT = Path(__file__).resolve().parent
INPUTS = ('Research_Report46.tex',)
def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--logs', type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        raise RuntimeError('Choose a new output path; existing artifacts are preserved.')
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH='1791072000', FORCE_SOURCE_DATE='1', TZ='UTC')
    with tempfile.TemporaryDirectory(prefix='report46-tex-') as temp:
        work = Path(temp)
        # The managed image may have package files but no generated TeX caches.
        # Build a private format and font map from installed vendor files only.
        dist = Path('/usr/share/texlive/texmf-dist')
        common = Path('/usr/share/texmf')
        probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], text=True, capture_output=True)
        if not probe.stdout.strip():
            if not dist.is_dir() or not common.is_dir():
                raise RuntimeError('Install a working TeX Live pdflatex toolchain before rebuilding.')
            env.update(
                TEXINPUTS='.:/usr/share/texlive/texmf-dist/tex//:/usr/share/texmf/tex//:',
                TFMFONTS='/usr/share/texlive/texmf-dist/fonts/tfm//:/usr/share/texmf/fonts/tfm//:',
                T1FONTS='/usr/share/texlive/texmf-dist/fonts/type1//:/usr/share/texmf/fonts/type1//:',
                ENCFONTS='/usr/share/texlive/texmf-dist/fonts/enc//:/usr/share/texmf/fonts/enc//:',
                TEXFORMATS=str(work), TEXFONTMAPS=str(work)+':',
                TEXMFVAR=str(work/'texmf-var'), TEXMFCONFIG=str(work/'texmf-config'))
            maps = [common/'fonts/map/dvips/lm/lm.map',
                    dist/'fonts/map/dvips/amsfonts/cm.map',
                    dist/'fonts/map/dvips/amsfonts/euler.map',
                    dist/'fonts/map/dvips/amsfonts/symbols.map']
            (work/'pdftex.map').write_bytes(b'\n'.join(p.read_bytes() for p in maps))
            init = subprocess.run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
                                   '-halt-on-error','-jobname=pdflatex','-progname=pdflatex',
                                   '*pdflatex.ini'],cwd=work,env=env,text=True,capture_output=True)
            if init.returncode:
                raise RuntimeError(init.stdout+init.stderr)
        for name in INPUTS:
            shutil.copyfile(ROOT / name, work / name)
        for _ in range(3):
            p = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                '-no-shell-escape', 'Research_Report46.tex'],
                               cwd=work, env=env, text=True, capture_output=True)
            if p.returncode:
                raise RuntimeError(p.stdout + p.stderr)
        log = (work / 'Research_Report46.log').read_text()
        if args.logs:
            args.logs.mkdir(parents=True, exist_ok=True)
            for name in ('Research_Report46.log', 'Research_Report46.aux',
                         'Research_Report46.toc', 'Research_Report46.pdf'):
                shutil.copyfile(work / name, args.logs / name)
        if 'Overfull \\hbox' in log or 'Overfull \\vbox' in log:
            raise RuntimeError('Overfull layout detected; inspect the saved build log.')
        if 'undefined references' in log or ('Citation' in log and 'undefined' in log):
            raise RuntimeError('Unresolved references in the build log.')
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(work / 'Research_Report46.pdf', output)
    print(json.dumps({'status': 'PASS', 'sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                      'bytes': output.stat().st_size, 'latex_runs': 3}, sort_keys=True))
if __name__ == '__main__':
    main()
