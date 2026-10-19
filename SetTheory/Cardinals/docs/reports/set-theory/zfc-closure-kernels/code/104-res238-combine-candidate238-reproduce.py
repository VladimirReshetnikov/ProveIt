#!/usr/bin/env python3
"""Replay construction/startup and, by default, all 8,386 unbounded guards.

All generated artifacts are written in a fresh temporary copy, so the bundled
evidence is left intact. Python 3.10+, standard library only, no -O or -OO.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick', action='store_true',
                    help='run exact construction/startup only, without the universal proof')
    ap.add_argument('--record', type=Path, help='save the concise replay receipt here')
    ap.add_argument('--keep-work', type=Path, help='keep the replay in this NEW directory')
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required.')
    temporary = None
    if args.keep_work:
        work = args.keep_work.resolve()
        require(not work.exists(), '--keep-work must name a new directory.')
    else:
        temporary = tempfile.TemporaryDirectory(prefix='zfc238-replay-')
        work = Path(temporary.name) / 'candidate238'
    shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    results = []
    begin = time.monotonic()

    def run(name, script, *arguments):
        print(f'Checking {name} ...', flush=True)
        started = time.monotonic()
        process = subprocess.run([sys.executable, '-B', script, *arguments],
                                 cwd=work, capture_output=True, text=True)
        (work / f'replay_{name}.log').write_text(process.stdout + process.stderr)
        require(process.returncode == 0, f'{name} failed:\n{process.stdout}\n{process.stderr}')
        results.append({'check': name, 'status': 'PASS',
                        'seconds': time.monotonic() - started})

    try:
        run('construction_and_startup', 'build_and_check.py')
        construction = json.loads((work / 'construction.json').read_text())
        require(construction['working_states'] == 238, 'Wrong state count')
        require(hashlib.sha256((work / 'zfc_combined238.tm').read_bytes()).hexdigest()
                == '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08',
                'Wrong canonical table')
        universal = None
        if not args.quick:
            run('universal_runtime', 'check_literal_runtime.py',
                '--table', 'zfc_combined238_old.tm', '--sites', 'sites_logical.json',
                '--states', '238', '--output', 'universal_runtime.json')
            universal = json.loads((work / 'universal_runtime.json').read_text())
            require(universal['status'] == 'UNIVERSAL_MATHEMATICAL_PASS',
                    'Universal proof did not pass')
            require(universal['cases'] == 8386, 'Incomplete instruction coverage')
        receipt = {
            'status': 'QUICK_CONSTRUCTION_STARTUP_PASS' if args.quick else 'FULL_BINARY_PASS',
            'checks': results, 'seconds': time.monotonic() - begin,
            'canonical_sha256': construction['canonical_sha256'],
            'working_states': 238, 'exact_blank_prefix_steps': 409835,
            'unbounded_guard_cases': 0 if universal is None else universal['cases'],
            'symbolic_rules': None if universal is None else universal['symbolic_steps'],
            'minimum_instruction_duration': None if universal is None else universal['minimum_actual_steps'],
            'scope': 'New binary table construction/startup/runtime; the inherited source-to-ZFC calibration is a separate proof dependency.',
        }
        if args.record:
            args.record.write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt, indent=2))
    finally:
        if temporary is not None:
            temporary.cleanup()

if __name__ == '__main__':
    main()
