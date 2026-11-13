"""Re-run the delivered certificate checks and optionally compile the report."""
from pathlib import Path
import argparse
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(arguments, directory):
    completed = subprocess.run(arguments, cwd=directory)
    if completed.returncode:
        raise SystemExit(completed.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='compile report.tex twice')
    options = parser.parse_args()
    run([sys.executable, 'verify.py'], ROOT / 'compact')
    run([sys.executable, 'verify.py'], ROOT / 'calculus')
    run([sys.executable, 'verify.py'], ROOT / 'implementation')
    if options.pdf:
        executable = shutil.which('pdflatex')
        if executable is None:
            raise SystemExit('pdflatex is required for --pdf')
        for _ in range(2):
            run([executable, '-interaction=nonstopmode', '-halt-on-error', 'report.tex'], ROOT)
    print('All requested reproduction steps completed.')


if __name__ == '__main__':
    main()
