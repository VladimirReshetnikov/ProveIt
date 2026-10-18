#!/usr/bin/env python3
"""Reproduce the Detour242 evidence, with an optional full expanded replay.

Python standard library only; no network, solver, Lean or Rocq required.
Fresh logs go into reproduced/; supplied evidence remains separately visible.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use python -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expanded', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / 'reproduced')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONUNBUFFERED='1')

    def run(name, script, *flags):
        command = [sys.executable, '-B', str(ROOT / script), *map(str, flags)]
        begin = time.monotonic()
        print(f'Running {name} ...', flush=True)
        with (out / (name + '.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                    stderr=subprocess.STDOUT)
        record = dict(check=name, exit_code=result.returncode,
                      seconds=round(time.monotonic() - begin, 6))
        records.append(record)
        if result.returncode:
            print((out / (name + '.log')).read_text()[-12000:])
            raise RuntimeError('Verification failed: ' + name)
        print(f'PASS {name} ({record["seconds"]:.2f} seconds)', flush=True)

    run('construction', 'code/build_machine.py')
    run('local-proof', 'code/verify_local_detour.py', '--output', out / 'local-proof.json')
    run('independent-review', 'code/review_detour242.py', '--package', ROOT,
        '--output', out / 'independent-review.json')
    run('blank', 'code/verify_blank.py', '--output', out / 'blank.json')
    run('affine-runtime', 'code/verify_runtime.py', '--output', out / 'affine-runtime.json')
    run('literal-runtime', 'code/verify_literal.py', '--output', out / 'literal-runtime.json',
        '--cases-output', out / 'literal-runtime-cases.json.gz')
    run('source-rotation', 'reference/rotation244/check_qt_rotation.py',
        '--reference', ROOT / 'reference/baseline245', '--output', out / 'source-rotation')
    logical = (out / 'source-rotation/right/sites_logical.json').read_bytes()
    assert logical == (ROOT / 'machine/sites_logical.json').read_bytes()
    run('equational1768', 'research/equational1768/verify_exact.py')
    if args.expanded:
        run('expanded-runtime', 'code/verify_runtime.py', '--expanded',
            '--output', out / 'expanded-runtime.json')
        expanded = json.loads((out / 'expanded-runtime.json').read_text())
        assert expanded['counts'] == {'cases': 8390, 'symbolic_rules': 2314880}
        assert expanded['literal_rows_covered'] == 484 and expanded['unused_rows'] == []
    summary = dict(status='PASS', expanded_executed=args.expanded, checks=records,
                   canonical_sha256=hashlib.sha256(
                       (ROOT / 'machine/zfc_detour242.tm').read_bytes()).hexdigest(),
                   scope='Ordinary finite certificates and exact executions. '
                         'Inherited consistency calibration is documented in report.tex. '
                         'No new proof-assistant endpoint is claimed.')
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
