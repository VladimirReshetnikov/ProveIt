#!/usr/bin/env python3
"""Run the delivered finite checks; no test establishes consistency."""
from __future__ import annotations
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(label, relative):
    result = subprocess.run(
        [sys.executable, '-B', str(ROOT / relative)],
        cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(f'{label} failed with status {result.returncode}')
    try:
        evidence = json.loads(result.stdout)
    except json.JSONDecodeError:
        sys.stderr.write(result.stdout)
        raise SystemExit(f'{label} did not emit a JSON result')
    print(f'PASS: {label}', flush=True)
    return evidence


def main():
    if not __debug__:
        raise SystemExit('Run without -O; finite verifiers use assertions.')
    results = {
        'checker': run('checker, examples, semantics and codec',
                       'code/verify_artifacts.py'),
        'independent_review': run('independent direct PSC comparison',
                                  'code/independent_review.py'),
        'diagonal_obstruction': run('logical obstruction regression',
                                    'code/diagonal_obstruction.py'),
        'engineering': run('independent table and register certificate',
                            'engineering/verify.py'),
    }
    results['all_passed'] = True
    results['finite_tests_prove_consistency'] = False
    results['new_literal_consistency_endpoint_proved'] = False
    out = ROOT / 'evidence' / 'reproduction.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(results, indent=2, sort_keys=True) + '\n')
    print('All finite checks passed. Evidence: evidence/reproduction.json')


if __name__ == '__main__':
    main()
