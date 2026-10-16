#!/usr/bin/env python3
"""Rebuild the report and optionally rerun experiments. No network access."""
from __future__ import annotations
import argparse
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def checked_run(command: list[str], transcript: Path) -> None:
    """Save combined output and raise an actionable error on failure."""
    completed = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True, check=False)
    transcript.parent.mkdir(parents=True, exist_ok=True)
    transcript.write_text(completed.stdout, encoding='utf-8')
    if completed.returncode:
        tail = '\n'.join(completed.stdout.splitlines()[-25:])
        raise RuntimeError(f'Command failed: {command}\nSee {transcript}\n{tail}')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tests', action='store_true', help='rerun all experiments')
    args = parser.parse_args()
    if args.tests:
        for script, transcript in [('hull_templates.py', 'metrics_run.txt'),
                                   ('finite_hulls.py', 'finite_run.txt'),
                                   ('test_templates.py', 'template_test_run.txt')]:
            checked_run([sys.executable, str(ROOT / 'code' / script)],
                        ROOT / 'results' / transcript)
            print(f'Passed: {script}')
    compiler = shutil.which('pdflatex')
    if compiler is None:
        raise RuntimeError('pdflatex not found. Install a LaTeX distribution; '
                           'the experiments can be run without LaTeX.')
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    for i in range(1, 4):
        checked_run([compiler, '-interaction=nonstopmode', '-halt-on-error',
                     '-output-directory=' + str(build),
                     str(ROOT / 'article' / 'exact_fiber_hulls.tex')],
                    build / f'pass{i}.stdout')
    log = (build / 'exact_fiber_hulls.log').read_text(encoding='utf-8', errors='replace')
    for marker in ['Overfull \\hbox', 'Overfull \\vbox',
                   'There were undefined references',
                   'Label(s) may have changed']:
        if marker in log:
            raise RuntimeError(f'LaTeX quality check found {marker!r}; see the log.')
    target = ROOT / 'article' / 'exact_fiber_hulls.pdf'
    shutil.copy2(build / target.name, target)
    print(f'Created {target}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError) as exc:
        print(f'Build error: {exc}', file=sys.stderr)
        raise SystemExit(1)
