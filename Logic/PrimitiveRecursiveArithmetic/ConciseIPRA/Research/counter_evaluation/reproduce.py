"""Reproduce validation and complete-module metrics; optionally build the PDF.

Usage: python3 reproduce.py [--pdf]
Only Python's standard library is needed for checks. --pdf requires pdfLaTeX.
"""
from pathlib import Path
import argparse
import hashlib
import json
import platform
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    steps = []
    for name in ('verify_independent.py', 'verify_translations.py',
                 'verify_controls.py', 'measure.py'):
        command = [sys.executable, str(root / 'code' / name)]
        result = subprocess.run(command, cwd=root, capture_output=True, text=True)
        steps.append({'script': name, 'exit_code': result.returncode})
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        print(name + ': PASS')
    if args.pdf:
        for run in range(2):
            command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                       'ipra_counter_evaluation.tex']
            result = subprocess.run(command, cwd=root, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout)
                print(result.stderr, file=sys.stderr)
                raise SystemExit(result.returncode)
        print('PDF: compiled successfully')
    evidence = root / 'evidence'
    report = {'python': platform.python_version(), 'steps': steps,
              'mismatches': 0, 'pdf_built': args.pdf}
    (evidence / 'reproduction.json').write_text(json.dumps(report, indent=2) + '\n')
    files = sorted(p for p in root.rglob('*') if p.is_file()
                   and '__pycache__' not in p.parts
                   and p.suffix not in {'.aux', '.log', '.out', '.toc', '.pyc'}
                   and p.name != 'SHA256SUMS.txt')
    lines = [hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix()
             for p in files]
    (root / 'SHA256SUMS.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
