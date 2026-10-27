#!/usr/bin/env python3
"""Replay all new finite certificates and compare ordinary/optimized Python.

Run from any directory. Results are written under replay_results by default,
so delivered evidence remains untouched. --output-dir can select another path.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=ROOT/'replay_results')
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    comparisons = []
    jobs = [('affine_certificate','check_affine_certificate.py'),
            ('twelve_certificate','check_twelve.py'),
            ('finite_algebra','check_affine_modes.py'),
            ('schedule','check_schedule.py')]
    for label, script in jobs:
        payloads = []
        for optimized in (False, True):
            result_path = args.output_dir/(label+('_optimized' if optimized else '')+'.json')
            command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT/'code'/script)]
            if label == 'schedule':
                command.append(str(result_path.resolve()))
            completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            require(completed.returncode == 0,
                    script+' failed: '+completed.stderr[-3000:]+completed.stdout[-1000:])
            if label != 'schedule':
                result_path.write_text(completed.stdout, encoding='utf-8')
            payload = json.loads(result_path.read_text(encoding='utf-8'))
            require(payload.get('status') in ('PASS','all exact finite checks passed'),
                    script+' did not report success')
            payloads.append(payload)
        require(payloads[0] == payloads[1], label+' differs under python -O')
        raw=(args.output_dir/(label+'.json')).read_bytes()
        comparisons.append({'check':label,'normal_equals_optimized':True,
                            'sha256':hashlib.sha256(raw).hexdigest()})
    result={'status':'PASS','python_version':sys.version.split()[0],
            'checks':comparisons,'interpretation':
            'Exact finite and arithmetic certificates; no end-to-end SAT or Lean build.'}
    (args.output_dir/'validation_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
