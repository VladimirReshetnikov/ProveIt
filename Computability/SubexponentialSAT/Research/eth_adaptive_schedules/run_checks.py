#!/usr/bin/env python3
"""Replay all exact checkers normally and with -O; preserve shipped evidence.

Only execution flags, elapsed time, and interpreter-version metadata are
ignored when comparing mathematical results. A failed check or mismatch exits
nonzero and is recorded in results/replay.json.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / 'results'
IGNORED_METADATA = frozenset({'elapsed_seconds', 'optimized_python',
                              'optimizations_enabled', 'python'})
CHECKERS = (
    ('check_kernels.py', 'checks.json', 'checks_optimized.json'),
    ('verify_schedule.py', 'schedule_checks.json', 'schedule_checks_optimized.json'),
    ('verify_cached_schedule.py', 'cached_checks.json', 'cached_checks_optimized.json'),
)


def mathematical_fields(value):
    if isinstance(value, dict):
        return {key: mathematical_fields(item) for key, item in value.items()
                if key not in IGNORED_METADATA}
    if isinstance(value, list):
        return [mathematical_fields(item) for item in value]
    return value


def main():
    RESULTS.mkdir(exist_ok=True)
    started = time.perf_counter()
    receipt = {'status': 'running', 'python': sys.version,
               'ignored_metadata_fields': sorted(IGNORED_METADATA),
               'source_sha256': {}, 'runs': [], 'comparisons': []}
    failure = None
    try:
        with tempfile.TemporaryDirectory(prefix='.replay-', dir=RESULTS) as temp:
            for script, normal_result, optimized_result in CHECKERS:
                source = ROOT / 'code' / script
                receipt['source_sha256'][script] = hashlib.sha256(source.read_bytes()).hexdigest()
                outputs = []
                for optimized, shipped_name in [(False, normal_result), (True, optimized_result)]:
                    command = [sys.executable, '-B']
                    if optimized:
                        command.append('-O')
                    command.append(str(source))
                    if script == 'check_kernels.py':
                        command += ['--output', str(Path(temp) / ('kernels_optimized.json' if optimized else 'kernels_normal.json'))]
                    process = subprocess.run(command, cwd=ROOT, text=True,
                                             capture_output=True, timeout=180)
                    run = {'checker': script, 'optimized': optimized,
                           'returncode': process.returncode, 'stderr': process.stderr}
                    receipt['runs'].append(run)
                    if process.returncode:
                        run['stdout'] = process.stdout
                        raise RuntimeError(f'{script} failed with exit code {process.returncode}')
                    output = json.loads(process.stdout)
                    run['output'] = output
                    if output.get('status', 'pass') != 'pass':
                        raise RuntimeError(f'{script} did not report success')
                    expected = json.loads((RESULTS / shipped_name).read_text())
                    equal = mathematical_fields(output) == mathematical_fields(expected)
                    receipt['comparisons'].append({'checker': script, 'optimized': optimized,
                                                   'shipped_result': shipped_name, 'equal': equal})
                    if not equal:
                        raise RuntimeError(f'{script} differs from the shipped mathematical result')
                    outputs.append(output)
                equal = mathematical_fields(outputs[0]) == mathematical_fields(outputs[1])
                receipt['comparisons'].append({'checker': script,
                                               'comparison': 'normal_vs_optimized', 'equal': equal})
                if not equal:
                    raise RuntimeError(f'{script} differs between normal and optimized Python')
        receipt['status'] = 'pass'
    except Exception as exc:
        failure = str(exc)
        receipt['status'] = 'fail'
        receipt['failure'] = failure
    receipt['elapsed_seconds'] = time.perf_counter() - started
    target = RESULTS / 'replay.json'
    target.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'runs': len(receipt['runs']),
                      'comparisons': len(receipt['comparisons']),
                      'output': 'results/replay.json',
                      **({'failure': failure} if failure else {})}, indent=2))
    return 1 if failure else 0


if __name__ == '__main__':
    raise SystemExit(main())
