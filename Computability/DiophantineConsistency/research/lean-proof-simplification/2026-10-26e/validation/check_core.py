#!/usr/bin/env python3
"""Serially check only the three core-only proposals with an existing Lean 4.32.0.

This script installs/downloads nothing and never modifies the upstream repo.
Usage: python3 validation/check_core.py --lean /trusted/lean-4.32.0-linux/bin/lean \
    --output-dir /tmp/proveit-core-results
The executable must be the already authorized official compiler. It is not
looked up on PATH. Results describe only these standalone files, not integration.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--output-dir', required=True, type=Path,
                        help='Results directory outside the sealed artifact tree')
    args = parser.parse_args()
    lean = args.lean.expanduser().resolve(strict=True)
    if not lean.is_file() or not os.access(lean, os.X_OK):
        parser.error('--lean must name an existing executable official compiler')
    base = Path(__file__).resolve().parent.parent
    output = args.output_dir.expanduser().resolve()
    if output == base or base in output.parents:
        parser.error('--output-dir must be outside the artifact tree to preserve its hashes')
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env.pop('LEAN_NUM_THREADS', None)
    version = subprocess.run([str(lean), '--version'], env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (output / 'lean-version.txt').write_text(version.stdout)
    if version.returncode or not re.search(r'\bversion 4\.32\.0\b', version.stdout):
        raise SystemExit('Refusing checks: expected Lean version 4.32.0; see lean-version.txt')
    files = [
        'SolutionTransport.lean',
        'checker_examples/IterationCore.lean',
        'checker_examples/ListLookupReplacements.lean',
    ]
    evidence = {
        'scope': 'standalone core-library proposals only; not project integration',
        'toolchain_path': str(lean),
        'toolchain_sha256': digest(lean),
        'toolchain_version': version.stdout.strip(),
        'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'sequential': True,
        'tests': [],
    }
    for rel in files:
        path = base / rel
        if not path.is_file():
            raise SystemExit(f'Missing candidate file: {path}')
        command = [str(lean), str(path)]
        before = digest(path)
        start = time.monotonic()
        run = subprocess.run(command, cwd=base, env=env, text=True,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        logfile = path.stem + '.log'
        (output / logfile).write_text(run.stdout)
        after = digest(path)
        # Treat the file-changing-under-test case as invalid, even on exit zero.
        sorry_warning = bool(re.search(r'declaration uses [\'\"]?sorry', run.stdout))
        sorry_axiom = 'sorryAx' in run.stdout
        status = ('pass' if run.returncode == 0 and before == after
                  and not sorry_warning and not sorry_axiom else 'fail')
        row = {'file': rel, 'sha256': before, 'sha256_after': after,
               'command': command, 'exit_code': run.returncode, 'status': status,
               'elapsed_seconds': elapsed, 'log': logfile,
               'sorry_warning': sorry_warning, 'sorry_axiom_in_log': sorry_axiom,
               'source_unchanged_during_test': before == after,
               'axiom_audit': ('named declarations printed by the candidate file; '
                              'anonymous examples have no individual axiom report')}
        evidence['tests'].append(row)
        (output / 'CORE_CHECKS.json').write_text(json.dumps(evidence, indent=2) + '\n')
        print(f'{status}: {rel} ({elapsed:.3f}s)')
    return 0 if all(t['status'] == 'pass' for t in evidence['tests']) else 1


if __name__ == '__main__':
    sys.exit(main())
