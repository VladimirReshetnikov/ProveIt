#!/usr/bin/env python3
"""Run the four supplied finite checkers sequentially and retain native JSON.

Python 3 standard library only. Run from any directory:
    python3 code/run_checks.py

The native schemas are preserved verbatim in validation/*_checks.json.
Separate stdout/stderr logs and checks_summary.json record this invocation.
A checker failure never replaces its previously successful native report.
These are finite regression checks, not universal mathematical proofs,
Lean kernel checking, or object-iPRA derivation checking.
"""
from __future__ import annotations

import json
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parents[1]
VALIDATION = ROOT / 'validation'
CHECKS = (
    ('finite', ROOT / 'code' / 'finite_topology.py', ('--max-n', '4'), 'stdout'),
    ('algebraic', ROOT / 'code' / 'algebraic_checks.py', (), 'file'),
    ('dimension', ROOT / 'code' / 'dimension' / 'validate.py', (), 'file'),
    ('sphere', ROOT / 'code' / 'sphere_checks.py', (), 'file'),
)


def run_one(name, script, args, mode):
    started = time.monotonic()
    report_path = VALIDATION / f'{name}_checks.json'
    result = {'checker': name, 'script': str(script.relative_to(ROOT)),
              'arguments': list(args), 'status': 'failed'}
    with tempfile.TemporaryDirectory(prefix=f'.{name}_run_',
                                     dir=VALIDATION) as temporary:
        native_tmp = Path(temporary) / 'native.json'
        command = [sys.executable, str(script), *args]
        if mode == 'file':
            command += ['--output', str(native_tmp)]
        try:
            completed = subprocess.run(command, cwd=script.parent,
                                       capture_output=True, text=True, check=False)
            (VALIDATION / f'{name}.stdout.log').write_text(completed.stdout)
            (VALIDATION / f'{name}.stderr.log').write_text(completed.stderr)
            result['return_code'] = completed.returncode
            if completed.returncode:
                result['error'] = 'Checker returned a nonzero exit status; inspect its logs.'
            else:
                raw = completed.stdout if mode == 'stdout' else native_tmp.read_text()
                native = json.loads(raw)
                result['native_status'] = native.get('status')
                if native.get('status') not in ('passed', 'all assertions passed'):
                    result['error'] = 'Checker JSON did not report a recognized passing status.'
                else:
                    # Keep the checker's own JSON bytes/schema rather than wrapping it.
                    report_path.write_text(raw)
                    result['report'] = str(report_path.relative_to(ROOT))
                    result['status'] = 'passed'
        except (OSError, ValueError) as exc:
            result['error'] = f'{type(exc).__name__}: {exc}'
    result['elapsed_seconds'] = round(time.monotonic() - started, 3)
    return result


def main():
    VALIDATION.mkdir(parents=True, exist_ok=True)
    results = []
    for name, script, args, mode in CHECKS:
        print(f'Running {name} checks...', flush=True)
        result = run_one(name, script, args, mode)
        results.append(result)
        print(f"  {result['status']} ({result['elapsed_seconds']:.3f} s)", flush=True)
    success = all(result['status'] == 'passed' for result in results)
    summary = {
        'status': 'passed' if success else 'failed',
        'python_version': platform.python_version(),
        'scope': 'Sequential finite regression checks; not universal, Lean, or object-iPRA proofs.',
        'checks': results,
    }
    summary_path = VALIDATION / 'checks_summary.json'
    summary_path.write_text(json.dumps(summary, indent=2) + '\n')
    print(f'Summary: {summary_path}', flush=True)
    return 0 if success else 1


if __name__ == '__main__':
    raise SystemExit(main())
