"""Reproduce the selected proof checks and complete-source measurements."""
from pathlib import Path
import argparse
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    for script in ['validation/verify.py', 'compact/reproduce.py']:
        print('Running', script, flush=True)
        subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT, check=True)
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / 'build_report.py'), '--pdf'],
                       cwd=ROOT, check=True)
    print('All reproduction commands passed.')

