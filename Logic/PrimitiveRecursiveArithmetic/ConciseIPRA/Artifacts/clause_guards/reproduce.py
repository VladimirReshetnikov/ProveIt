"""Run all included evidence suites; optionally rebuild the PDF.

This orchestration script is not imported by either standalone checker.
Use CPython 3.12.14 for the exact reported source-size measurements.
"""
from pathlib import Path
import argparse
import json
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true', help='also rebuild report.pdf')
    args = parser.parse_args()
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    summaries = {}
    for name in ('diagonal', 'mirror'):
        completed = subprocess.run(
            [sys.executable, 'verify.py'], cwd=ROOT / name,
            text=True, capture_output=True, check=False,
        )
        (evidence / (name + '_run.txt')).write_text(
            completed.stdout + completed.stderr, encoding='utf-8')
        if completed.returncode:
            raise RuntimeError(f'{name} verification failed; inspect its run log')
        data = json.loads((ROOT / name / 'results.json').read_text())
        if data['status'] != 'all checks passed':
            raise RuntimeError(f'{name} did not report success')
        summaries[name] = {
            'status': data['status'],
            'positive_certificates': len(data['positive']),
            'negative_certificates': len(data['negative']),
            'process_checks': data['process_checks'],
            'metrics': data['metrics'],
        }
        print(f'{name}: all checks passed; '
              f'{len(data["positive"])} positive, '
              f'{len(data["negative"])} negative, '
              f'{data["process_checks"]} command-line checks')
    if args.pdf:
        for pass_number in range(3):
            completed = subprocess.run(
                ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                 '-file-line-error', 'report.tex'],
                cwd=ROOT, text=True, capture_output=True, check=False,
            )
            (evidence / f'latex_pass_{pass_number + 1}.txt').write_text(
                completed.stdout + completed.stderr, encoding='utf-8')
            if completed.returncode:
                raise RuntimeError('PDF build failed; inspect the LaTeX log')
        print('PDF rebuilt: report.pdf')
    (evidence / 'reproduction.json').write_text(
        json.dumps({'python': sys.version, 'suites': summaries}, indent=2) + '\n',
        encoding='utf-8',
    )


if __name__ == '__main__':
    main()
