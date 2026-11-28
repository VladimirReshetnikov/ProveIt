#!/usr/bin/env python3
"""Rebuild the two papers, optionally rerunning checks and rendering PDF pages."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
PAPERS = ('sharp_reciprocal_zero_inequalities', 'central_derivatives_note')


def run(command: list[str], cwd: Path = ROOT) -> str:
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    return result.stdout


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='Rerun symbolic, exact and numerical checks.')
    parser.add_argument('--render', action='store_true', help='Render PDF pages with pdftoppm into qa/.')
    args = parser.parse_args()
    if args.verify:
        checks = ROOT / 'verification'
        print('Running reciprocal-bound checks...', flush=True)
        run([sys.executable, str(checks / 'verify_reciprocal_bounds.py')])
        for suffix in ('pdf', 'png'):
            generated = checks / f'reciprocal_bounds_figure.{suffix}'
            shutil.copy2(generated, ROOT / 'figures' / f'reciprocal_bounds.{suffix}')
            generated.unlink()
        data = json.loads((checks / 'verification_results.json').read_text())
        print(f"Passed {data['square_optimizer_checks']['cases_checked']} exact square-prefix cases.", flush=True)
        print('Running high-precision derivative illustrations...', flush=True)
        run([sys.executable, str(checks / 'verify_central_derivatives.py')])
        data = json.loads((checks / 'central_derivatives_checks.json').read_text())
        print(f"Recorded {len(data['cases'])} derivative and {len(data['hankel_range_illustrations_not_interval_certificates'])} matrix-range illustrations.", flush=True)
    if not shutil.which('pdflatex'):
        raise SystemExit('pdflatex is required to compile the papers.')
    for name in PAPERS:
        for _ in range(2):
            run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', name + '.tex'])
        log = (ROOT / (name + '.log')).read_text(errors='replace')
        problems = [line for line in log.splitlines() if
                    'Overfull' in line or 'undefined' in line.lower() or 'Rerun to get' in line]
        if problems:
            raise SystemExit(name + ': layout/reference check failed:\n' + '\n'.join(problems))
        print('Compiled ' + name + '.pdf', flush=True)
        if args.render:
            if not shutil.which('pdftoppm'):
                raise SystemExit('pdftoppm is required for --render.')
            dest = ROOT / 'qa' / name
            dest.mkdir(parents=True, exist_ok=True)
            run(['pdftoppm', '-png', '-r', '120', str(ROOT / (name + '.pdf')), str(dest / 'page')])
            print('Rendered pages in ' + str(dest.relative_to(ROOT)), flush=True)
    print('Build complete. Rebuilt PDF metadata may differ from the archived SHA-256 hashes.')


if __name__ == '__main__':
    main()
