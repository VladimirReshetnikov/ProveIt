"""Run the supplied offline checks and optionally rebuild the PDF."""
from pathlib import Path
import argparse
import json
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    evidence = root / 'evidence'
    evidence.mkdir(exist_ok=True)
    records = []

    def run(relative, save_stdout=None):
        p = subprocess.run([sys.executable, str(root / relative)], cwd=root,
                           text=True, capture_output=True)
        records.append({'command': relative, 'exit_code': p.returncode})
        if p.returncode:
            print(p.stdout)
            print(p.stderr, file=sys.stderr)
            raise SystemExit(p.returncode)
        if save_stdout:
            value = json.loads(p.stdout)
            (evidence / save_stdout).write_text(json.dumps(value, indent=2) + '\n')
        print(relative + ': PASS')

    run('code/uniqueness/measure.py')
    run('code/uniqueness/verify.py')
    run('code/compact/verify.py')
    run('tests/ur_predecessor_sanity.py', 'ur_predecessor_sanity.json')
    run('tests/validate_ur_reflection.py')
    produced = root / 'tests' / 'ur_reflection_validation.json'
    if produced.exists():
        (evidence / produced.name).write_bytes(produced.read_bytes())
        produced.unlink()
    if args.pdf:
        run('build_report.py')
        for _ in range(2):
            p = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                '-halt-on-error', 'report.tex'], cwd=root,
                               text=True, capture_output=True)
            if p.returncode:
                print(p.stdout[-12000:])
                raise SystemExit(p.returncode)
        records.append({'command': 'pdflatex (two passes)', 'exit_code': 0})
        print('report.pdf: built')
    (evidence / 'reproduction.json').write_text(json.dumps(records, indent=2) + '\n')


if __name__ == '__main__':
    main()
