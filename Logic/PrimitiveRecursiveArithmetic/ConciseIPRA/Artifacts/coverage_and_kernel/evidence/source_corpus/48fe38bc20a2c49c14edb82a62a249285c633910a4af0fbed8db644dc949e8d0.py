"""Reproduce the delivered source accounting and finite checks offline."""
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(relative_path):
    process = subprocess.run([sys.executable, str(ROOT / relative_path)],
                             cwd=ROOT, text=True, capture_output=True, timeout=180)
    if process.returncode:
        print(process.stdout)
        print(process.stderr, file=sys.stderr)
        raise SystemExit(process.returncode)
    try:
        result = json.loads(process.stdout)
    except json.JSONDecodeError:
        result = {'output': process.stdout.strip()}
    return result


def main():
    measurement = run('measure.py')
    checker = run('tests/verify.py')
    arithmetic = run('tests/arithmetic_checks.py')
    countermodel = run('tests/zero_source_countermodel.py')
    receipt = {
        'status': 'PASS',
        'python': platform.python_version(),
        'checker_suite': checker,
        'arithmetic_diagnostics': arithmetic,
        'zero_source_counterinterpretation': countermodel,
        'measurements': measurement,
        'scope': 'Finite implementation checks and diagnostics. Written metatheorem proofs are not proof-assistant verified.',
    }
    (ROOT / 'evidence' / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
