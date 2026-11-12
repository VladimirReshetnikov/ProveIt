"""Offline verification of source identities, metrics and real certificates.

No repository access or theorem prover is required. The default run does
not modify package files. Use --no-manifest only while authoring the package.
"""
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'tests'))
import build_cases
import measure


def check_manifest():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for row in manifest['files']:
        raw = (ROOT / row['path']).read_bytes()
        if len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != row['sha256']:
            raise ValueError('Payload changed: ' + row['path'])
    return len(manifest['files'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-manifest', action='store_true')
    args = parser.parse_args()
    manifest_count = None if args.no_manifest else check_manifest()
    measurements = measure.collect()
    stored = json.loads((ROOT / 'tests/cases.json').read_text())
    cases = build_cases.build_cases()
    # Prose annotations may be clarified, but proof data and verdicts must reproduce.
    key = lambda row: (row['name'], row['packet'], row['accept'])
    if [key(row) for row in cases] != [key(row) for row in stored]:
        raise ValueError('Named certificate regeneration mismatch')
    runs = 0
    accepts = 0
    for name in ('checker.py', 'checker_bytes.py', 'checker_joint.py'):
        for optimized in (False, True):
            for case in cases:
                run = subprocess.run([sys.executable, *(['-O'] if optimized else []),
                                      str(ROOT / 'code' / name)],
                                     input=json.dumps(case['packet']), text=True,
                                     capture_output=True, timeout=40)
                accepted = run.returncode == 0 and run.stdout.strip() == 'ACCEPT'
                if accepted != case['accept']:
                    raise ValueError(f"Unexpected verdict: {name}/{case['name']}/optimized={optimized}: {run.stderr[-300:]}")
                runs += 1
                accepts += accepted
    eager = subprocess.run([sys.executable, str(ROOT / 'tests/eager_model_check.py')],
                           text=True, capture_output=True, check=True)
    result = {'status': 'PASS', 'manifest_files': manifest_count,
              'frozen_python_sources_remeasured': measurements['corpus_sources'],
              'driver_only_controls_verified': measurements['matched_control_count'],
              'cases': len(cases), 'cli_runs': runs, 'accepted': accepts,
              'rejected': runs - accepts, 'mismatches': 0,
              'eager_countermodel_check': eager.stdout.strip(),
              'programs': measurements['programs']}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
