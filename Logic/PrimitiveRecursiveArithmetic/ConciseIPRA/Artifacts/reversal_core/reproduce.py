"""Reproduce complete-checker measurements and the portable verification suite."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(arguments):
    result = subprocess.run(arguments, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print(result.stdout)
        print(result.stderr)
        raise SystemExit(result.returncode)
    if result.stdout.strip():
        print(result.stdout.strip())


def build_pdf():
    if not shutil.which('pdflatex'):
        raise SystemExit('PDF build requires pdflatex and the LaTeX packages listed in the source.')
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
               '-output-directory', str(build), 'ipra_reversal_core.tex']
    for _ in range(3):
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout[-12000:])
            print(result.stderr)
            raise SystemExit(result.returncode)
    shutil.copy2(build / 'ipra_reversal_core.pdf', ROOT / 'ipra_reversal_core.pdf')
    print('Built ipra_reversal_core.pdf')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='Also compile the self-contained LaTeX source')
    parser.add_argument('--pdf-only', action='store_true', help='Compile the report without rerunning checks')
    parser.add_argument('--parser-audit', action='store_true', help='Also regenerate the finite parser comparison')
    args = parser.parse_args()
    if not args.pdf_only:
        run([sys.executable, 'tools/measure.py'])
        run([sys.executable, 'tests/test_rev.py', '--receipt',
             str(ROOT / 'evidence/all_rev_reproduction.json')])
        run([sys.executable, 'tests/test_rev.py', '--single-checker',
             str(ROOT / 'code/readable_checker.py'), '--profile', 'full',
             '--zero-neutral', '--typed', '--receipt',
             str(ROOT / 'evidence/readable_reproduction.json')])
        run([sys.executable, 'tools/audit_zero_neutral.py'])
        if args.parser_audit:
            run([sys.executable, 'tools/audit_validators.py'])
    if args.pdf or args.pdf_only:
        build_pdf()


if __name__ == '__main__':
    main()
