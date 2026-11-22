#!/usr/bin/env python3
"""Replay the four independent exact-arithmetic demonstrations."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise SystemExit('Run Python without -O: these examples use assertions.')
    scripts = ['measure_examples.py', 'operator_logic_examples.py',
               'complex_integral_examples.py', 'homological_examples.py']
    results = []
    for script in scripts:
        source = ROOT / 'code' / script
        run = subprocess.run([sys.executable, str(source)], cwd=ROOT,
                             text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT)
        item = {'program': 'code/' + script, 'returncode': run.returncode,
                'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'output': run.stdout.strip()}
        results.append(item)
        if run.returncode:
            print(run.stdout)
            raise SystemExit(f'Failed: {script}')
    output = {'status': 'passed', 'python': sys.version, 'programs': results,
              'scope': 'Finite exact implementation checks; no universal-proof inference.'}
    (ROOT / 'validation' / 'integration_checks.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'programs': len(results)}))


if __name__ == '__main__':
    main()
