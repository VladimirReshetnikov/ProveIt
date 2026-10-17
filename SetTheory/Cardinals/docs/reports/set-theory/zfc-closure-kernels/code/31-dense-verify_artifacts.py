#!/usr/bin/env python3
"""Run the delivered finite checks in a fresh, disposable artifact copy.

The core requires only Python 3; an optional C++17 compiler speeds one replay.
With both --repo and --upstream, also rebuild the frozen runtime and verify
the saved grammar certificates against the pinned external project sources.
This driver does not search for new proofs or establish a consistency theorem.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
DIRECTORIES = ('initializer_experiments', 'theory_scope', 'scope_audit',
               'dense_qnand', 'machine_experiments')


def run_check(root, title, arguments, evidence):
    started = time.monotonic()
    completed = subprocess.run(
        [sys.executable, *map(str, arguments)], cwd=root,
        env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'},
        text=True, capture_output=True)
    if completed.returncode:
        sys.stderr.write(completed.stdout)
        sys.stderr.write(completed.stderr)
        raise RuntimeError(f'{title}: process exit {completed.returncode}')
    result = json.loads((root / evidence).read_text())
    if 'status' in result and result['status'] != 'PASS':
        raise RuntimeError(f'{title}: unexpected result status')
    print(f'PASS: {title}', flush=True)
    return {'check': title, 'status': 'PASS',
            'elapsed_seconds': round(time.monotonic() - started, 3),
            'evidence': evidence, 'result': result}


def main():
    if not __debug__:
        raise SystemExit('Run without -O: assertions are part of these finite audits.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--upstream', type=Path)
    parser.add_argument('--output', type=Path,
                        help='Optional aggregate result path; default only prints a summary.')
    args = parser.parse_args()
    if (args.repo is None) != (args.upstream is None):
        parser.error('--repo and --upstream must be supplied together')
    checks = []
    with tempfile.TemporaryDirectory(prefix='zfc-report-verify-') as tmp:
        root = Path(tmp)
        for directory in DIRECTORIES:
            shutil.copytree(ROOT / directory, root / directory,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        jobs = [
            ('Regenerate and replay the exact initializer',
             ['initializer_experiments/verify_initializer.py'],
             'initializer_experiments/output/initializer_verification.json'),
            ('Independent Python literal-table and tape audit',
             ['initializer_experiments/independent_python_audit.py'],
             'initializer_experiments/output/independent_python_replay.json'),
            ('Default-index checker transport finite audit',
             ['theory_scope/check_default_indices.py'],
             'theory_scope/default_indices_results.json'),
            ('Independent scope and adversarial certificate audit',
             ['scope_audit/independent_scope_audit.py'],
             'scope_audit/independent_scope_results.json'),
            ('Dense quantified-NAND codec and semantics',
             ['dense_qnand/check_dense_qnand.py'],
             'dense_qnand/dense_qnand_results.json'),
        ]
        for title, command, evidence in jobs:
            checks.append(run_check(root, title, command, evidence))
        if args.repo is not None:
            repo, upstream = args.repo.resolve(), args.upstream.resolve()
            checks.append(run_check(root, 'Rebuild frozen runtime from pinned sources',
                ['initializer_experiments/extract_runtime.py', '--repo', repo,
                 '--upstream', upstream, '--output',
                 root / 'initializer_experiments/output/independent_runtime_rebuild.json'],
                'initializer_experiments/output/independent_runtime_rebuild.json'))
            checks.append(run_check(root, 'Validate saved grammar and local-join certificates',
                ['machine_experiments/validate_experiments.py', '--repo', repo,
                 '--upstream', upstream], 'machine_experiments/validation.json'))
    report = {'status': 'PASS', 'checks': checks,
              'checks_run': len(checks),
              'source_checkouts_used': args.repo is not None,
              'delivered_evidence_modified': False,
              'full_machine_consistency_theorem_checked': False,
              'new_sub253_machine': False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'All {len(checks)} requested finite checks passed.')


if __name__ == '__main__':
    main()
