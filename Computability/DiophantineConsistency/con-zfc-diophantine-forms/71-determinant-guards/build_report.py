#!/usr/bin/env python3
"""Compile the complete article; no network or nonstandard Python package."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    executable = shutil.which('pdflatex')
    if not executable:
        raise SystemExit('pdflatex is required; install TeX Live with the packages listed in report.tex.')
    env = dict(os.environ)
    env.setdefault('SOURCE_DATE_EPOCH', '1792713600')
    env.setdefault('FORCE_SOURCE_DATE', '1')
    with tempfile.TemporaryDirectory(prefix='con_zfc_pdf_') as temporary:
        command = [executable, '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-file-line-error',
                   '-output-directory='+temporary, 'report.tex']
        for _ in range(3):
            process = subprocess.run(command, cwd=ROOT, env=env,
                                     capture_output=True, text=True)
            if process.returncode:
                raise SystemExit(process.stdout[-10000:]+'\n'+process.stderr)
        log = (Path(temporary)/'report.log').read_text(errors='replace')
        warnings = [line for line in log.splitlines()
                    if 'Overfull' in line or 'Warning:' in line or 'undefined' in line]
        if warnings:
            print('\n'.join(warnings))
        shutil.copyfile(Path(temporary)/'report.pdf', ROOT/'report.pdf')
        print('Compiled report.pdf ('+str((ROOT/'report.pdf').stat().st_size)+' bytes).')


if __name__ == '__main__':
    main()
