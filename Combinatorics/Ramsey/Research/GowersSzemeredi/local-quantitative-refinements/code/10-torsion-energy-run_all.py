#!/usr/bin/env python3
"""Run all mathematical diagnostics and record their actual outputs.

These finite checks supplement, and do not replace, the general proofs.
No network access is used. The complex-function diagnostics require NumPy.
"""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


def run_one(path):
    start = time.monotonic()
    proc = subprocess.run([sys.executable, str(path)], capture_output=True, text=True)
    result = {
        'script': 'verification/' + path.name,
        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'exit_code': proc.returncode,
        'elapsed_seconds': round(time.monotonic() - start, 3),
        'stdout': proc.stdout,
        'stderr': proc.stderr,
    }
    try:
        result['structured_output'] = json.loads(proc.stdout)
    except json.JSONDecodeError:
        pass
    return result


def main():
    here = Path(__file__).resolve().parent
    names = ['verify_density_phase.py', 'verify_structural.py',
             'verify_torsion.py', 'verify_polynomial.py']
    with ThreadPoolExecutor(max_workers=4) as pool:
        results = list(pool.map(run_one, [here / n for n in names]))
    versions = {}
    for name in ['numpy', 'matplotlib']:
        try:
            versions[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            versions[name] = None
    payload = {
        'description': 'Finite diagnostics; general claims are proved in the article.',
        'completed_at_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(),
        'dependencies': versions,
        'all_passed': all(r['exit_code'] == 0 for r in results),
        'checks': results,
    }
    destination = here.parent / 'verification_results.json'
    destination.write_text(json.dumps(payload, indent=2) + '\n')
    for result in results:
        print(f"{result['script']}: exit {result['exit_code']} ({result['elapsed_seconds']} s)")
        print(result['stdout'].strip())
        if result['stderr'].strip():
            print(result['stderr'].strip(), file=sys.stderr)
    print(f'Results written to {destination.name}')
    return 0 if payload['all_passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

