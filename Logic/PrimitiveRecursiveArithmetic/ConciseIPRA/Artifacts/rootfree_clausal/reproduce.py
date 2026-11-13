"""Reproduce all selected checker tests and measurements without network access."""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true', help='Also rebuild the standalone TeX and PDF')
    args = parser.parse_args()
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    tasks = [
        ('validate_raw.py', 'raw_validation.json'),
        ('validate.py', 'validation.json'),
        ('validate_zero_base.py', 'zero_base_validation.json'),
        ('measure.py', 'metrics.json'),
    ]
    for script, result in tasks:
        process = subprocess.run([sys.executable, str(ROOT / 'code' / script)],
                                 cwd=ROOT / 'code', capture_output=True, text=True)
        if process.returncode:
            sys.stderr.write(process.stdout + process.stderr)
            raise SystemExit(process.returncode)
        shutil.copy2(ROOT / 'code' / result, evidence / result)
        data = json.loads((evidence / result).read_text())
        if 'results' in data:
            print('Measurements reproduced under Python ' + data['python'])
        else:
            print(script + ': ' + str(data['positive_certificates']) + ' positives, '
                  + str(data['negative_certificates']) + ' negatives, '
                  + str(data['process_checks']) + ' CLI runs; '
                  + str(data['unexpected_outcomes']) + ' unexpected outcomes')
    if args.pdf:
        subprocess.run([sys.executable, str(ROOT / 'build_report.py')], cwd=ROOT, check=True)
        for _ in range(3):
            result = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                     'report.tex'], cwd=ROOT, capture_output=True, text=True)
            if result.returncode:
                sys.stderr.write(result.stdout[-10000:] + result.stderr)
                raise SystemExit(result.returncode)
        print('Rebuilt report.pdf.')
    print('All selected implementation checks passed. These checks are not a proof-assistant formalization.')


if __name__ == '__main__':
    main()
