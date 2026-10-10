"""Replay exact certificates, then optionally run numerical diagnostics.

Run from any directory with Python 3.11 or later::

    python code/verify_all.py
    python -O code/verify_all.py --diagnostics

Exact replay establishes the claims stated by each certificate; in particular,
the S14 certificate proves proximity, not the conjectured equality. Numerical
diagnostics provide consistency checks and are not substitutes for proofs.
Full child-process output is saved to verification/replay_report.json.
"""
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import time


BASE = Path(__file__).resolve().parents[1]
REPORT_PATH = BASE / 'verification' / 'replay_report.json'
EXACT_SCRIPTS = (
    'verify_kernel.py',
    'verify_order_constants.py',
    'verify_mesh.py',
    'verify_s14.py',
)
DIAGNOSTIC_SCRIPTS = (
    'kernel_diagnostics.py',
    'order_asymptotic_diagnostics.py',
    'verify_negative_orders.py',
    'verify_mixed_generator.py',
    'audit_s14.py',
)


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def command_for(script):
    command = [sys.executable]
    # Propagate optimized mode so it also exercises unconditional child checks.
    if sys.flags.optimize:
        command.append('-O')
    command.append(str(Path('code') / script))
    return command


def run_script(script, category):
    command = command_for(script)
    record = {
        'script': str(Path('code') / script),
        'category': category,
        'command': command,
        'started_at_utc': utc_now(),
    }
    start = time.monotonic()
    print(f'[{category}] {script}: ', end='', flush=True)
    try:
        result = subprocess.run(
            command,
            cwd=BASE,
            capture_output=True,
            text=True,
            encoding='utf-8',
            errors='replace',
            check=False,
        )
        record.update({
            'return_code': result.returncode,
            'status': 'passed' if result.returncode == 0 else 'failed',
            'stdout': result.stdout,
            'stderr': result.stderr,
        })
    except OSError as exc:
        record.update({
            'return_code': None,
            'status': 'failed',
            'stdout': '',
            'stderr': f'{type(exc).__name__}: {exc}',
        })
    record['seconds'] = round(time.monotonic() - start, 6)
    record['finished_at_utc'] = utc_now()
    print(f"{record['status'].upper()} ({record['seconds']:.2f}s)", flush=True)
    if record['status'] == 'failed' and record['stderr'].strip():
        print('  ' + record['stderr'].strip().splitlines()[-1], flush=True)
    return record


def write_report(report):
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    temporary = REPORT_PATH.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    temporary.replace(REPORT_PATH)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        '--diagnostics', action='store_true',
        help='Run numerical diagnostics after every exact replay passes',
    )
    args = parser.parse_args()
    start = time.monotonic()
    report = {
        'schema_version': 1,
        'started_at_utc': utc_now(),
        'package_directory': str(BASE),
        'python_executable': sys.executable,
        'python_version': sys.version,
        'parent_optimization_level': sys.flags.optimize,
        'child_optimization_level': 1 if sys.flags.optimize else 0,
        'diagnostics_requested': args.diagnostics,
        'status': 'running',
        'scripts': [],
    }
    write_report(report)
    for script in EXACT_SCRIPTS:
        report['scripts'].append(run_script(script, 'exact_replay'))
        write_report(report)
    exact_passed = all(item['status'] == 'passed' for item in report['scripts'])
    report['exact_replays_passed'] = exact_passed
    if args.diagnostics and exact_passed:
        for script in DIAGNOSTIC_SCRIPTS:
            report['scripts'].append(run_script(script, 'numerical_diagnostic'))
            write_report(report)
    elif args.diagnostics:
        for script in DIAGNOSTIC_SCRIPTS:
            report['scripts'].append({
                'script': str(Path('code') / script),
                'category': 'numerical_diagnostic',
                'command': command_for(script),
                'status': 'skipped',
                'reason': 'At least one exact replay failed',
                'return_code': None,
                'seconds': 0.0,
                'stdout': '',
                'stderr': '',
            })
        print('Numerical diagnostics skipped because an exact replay failed.',
              flush=True)
    counts = {
        status: sum(item['status'] == status for item in report['scripts'])
        for status in ('passed', 'failed', 'skipped')
    }
    report['counts'] = counts
    report['status'] = 'failed' if counts['failed'] else 'passed'
    report['seconds'] = round(time.monotonic() - start, 6)
    report['finished_at_utc'] = utc_now()
    write_report(report)
    print(f"Replay {report['status'].upper()}: {counts['passed']} passed, "
          f"{counts['failed']} failed, {counts['skipped']} skipped "
          f"({report['seconds']:.2f}s).", flush=True)
    print('Report: verification/replay_report.json', flush=True)
    return 1 if counts['failed'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
