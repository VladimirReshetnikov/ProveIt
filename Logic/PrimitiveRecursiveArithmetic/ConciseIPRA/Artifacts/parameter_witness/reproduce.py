#!/usr/bin/env python3
"""Reproduce finite executable evidence; this is not a formal theorem prover."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(path):
    completed = subprocess.run([sys.executable, str(path)], cwd=ROOT,
                               text=True, capture_output=True, check=True)
    return completed.stdout


def main():
    checker_output = run(ROOT / 'checker/reproduce.py')
    metrics = json.loads((ROOT / 'checker/METRICS.json').read_text())
    validation = json.loads((ROOT / 'checker/VALIDATION.json').read_text())
    checker = {'metrics': metrics,
               'validation': {k: v for k, v in validation.items() if k != 'receipts'}}
    arithmetic = json.loads(run(ROOT / 'code/check_scalar_arithmetic.py'))
    evidence = ROOT / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'checker_reproduction_stdout.txt').write_text(checker_output)
    for filename, value in [('checker_summary.json', checker),
                            ('scalar_arithmetic_checks.json', arithmetic)]:
        (evidence / filename).write_text(json.dumps(value, indent=2) + '\n')
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
    verified = 0
    for item in provenance['reference_files']:
        data = (ROOT / item['local_path']).read_bytes()
        if hashlib.sha256(data).hexdigest() != item['sha256']:
            raise ValueError('Reference hash mismatch: ' + item['local_path'])
        if 'git_blob_sha1' in item:
            blob = b'blob ' + str(len(data)).encode() + b'\0' + data
            if hashlib.sha1(blob).hexdigest() != item['git_blob_sha1']:
                raise ValueError('Git blob mismatch: ' + item['local_path'])
        verified += 1
    summary = {'checker': checker['validation'],
               'arithmetic': arithmetic,
               'reference_hashes_verified': verified,
               'scope': 'Finite executable evidence; universal mathematical proofs are written in the report.'}
    (evidence / 'reproduction.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
