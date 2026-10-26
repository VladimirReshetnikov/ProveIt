#!/usr/bin/env python3
"""Regenerate and compile the standalone report with no shell escape."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def main():
    if shutil.which('pdflatex') is None:
        raise SystemExit('pdflatex is required; install TeX Live with the source packages.')
    for script in ['code/export_report.py', 'code/check_report.py']:
        subprocess.run([sys.executable, '-B', str(ROOT / script)], check=True, cwd=ROOT)
    source = ROOT / 'ConZFC_Exact_Contractions.tex'
    with tempfile.TemporaryDirectory(prefix='conzfc-report-') as temp:
        build = Path(temp)
        shutil.copy2(source, build / source.name)
        for run in range(3):
            done = subprocess.run(
                ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', source.name], cwd=build,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if done.returncode:
                print(done.stdout)
                raise SystemExit(done.returncode)
        log = (build / source.with_suffix('.log').name).read_text()
        if 'Overfull ' in log or 'undefined references' in log:
            print(log)
            raise SystemExit('Report has an overfull box or unresolved reference.')
        destination = source.with_suffix('.pdf')
        shutil.copy2(build / destination.name, destination)
    print('Built ' + str(destination))
    print('PDF metadata may change its manifest hash; coefficient checks are independent.')


if __name__ == '__main__':
    main()
