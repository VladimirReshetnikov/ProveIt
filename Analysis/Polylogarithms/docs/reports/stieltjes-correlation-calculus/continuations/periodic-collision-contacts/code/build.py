#!/usr/bin/env python3
"""Build the research article without leaving TeX intermediates in the package."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
STEM = 'Periodic_Stieltjes_Collisions'


def main() -> None:
    executable = shutil.which('pdflatex')
    if executable is None:
        raise SystemExit('pdflatex was not found. Install a TeX distribution with the packages listed in the article preamble.')
    source = ROOT / f'{STEM}.tex'
    if not source.is_file():
        raise SystemExit(f'Missing source: {source}')
    with tempfile.TemporaryDirectory(prefix='proveit-periodic-collision-') as temporary:
        work = Path(temporary)
        shutil.copy2(source, work / source.name)
        environment = os.environ.copy()
        # Suppress a dependency on the machine's local timezone in the PDF date.
        environment['TZ'] = 'UTC'
        log = ''
        for pass_number in range(1, 4):
            command = [executable, '-interaction=nonstopmode', '-halt-on-error', source.name]
            result = subprocess.run(command, cwd=work, env=environment, capture_output=True, text=True, timeout=120)
            if result.returncode != 0:
                (ROOT / 'data' / 'build_failure.log').write_text(result.stdout + '\n' + result.stderr)
                raise SystemExit(f'LaTeX failed on pass {pass_number}; see data/build_failure.log.')
            log = (work / f'{STEM}.log').read_text(errors='replace')
        warnings = [line for line in log.splitlines() if any(text in line for text in (
            'Warning:', 'Overfull', 'undefined references', 'multiply defined'))]
        destination = ROOT / f'{STEM}.pdf'
        shutil.copy2(work / destination.name, destination)
        receipt = {
            'status': 'compiled', 'passes': 3, 'engine': executable,
            'engine_version': subprocess.run([executable, '--version'], capture_output=True, text=True).stdout.splitlines()[0],
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'pdf_sha256': hashlib.sha256(destination.read_bytes()).hexdigest(),
            'warnings': warnings,
            'note': 'Compilation is not mathematical or visual validation. PDF metadata may differ on a rebuild.'
        }
        (ROOT / 'data' / 'build_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
