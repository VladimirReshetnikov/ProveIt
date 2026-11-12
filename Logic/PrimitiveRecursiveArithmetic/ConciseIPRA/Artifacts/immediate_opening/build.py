"""Compile the report and regenerate its complete-source measurement receipt."""
from pathlib import Path
import subprocess
import sys
from build_pdf import build

ROOT = Path(__file__).resolve().parent


def main():
    subprocess.run(
        [sys.executable, str(ROOT / 'measure.py'), '--output',
         str(ROOT / 'evidence/measurements.json')], check=True, cwd=ROOT
    )
    build(ROOT / 'report.tex', ROOT / 'report.pdf', ROOT / 'evidence/pdf_build.log')
    print('Built report.pdf')


if __name__ == '__main__':
    main()
