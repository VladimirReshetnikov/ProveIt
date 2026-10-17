#!/usr/bin/env python3
"""Reproduce the finite evidence in this archive; Python standard library only.

The root manifest is checked before any supplied program is executed.
Preferred-kernel results are regenerated in a temporary directory and
compared structurally, excluding only elapsed time. The nested numerical
package enforces byte-identical reproduction of its own artifacts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def run(script, *arguments):
    command = [sys.executable, '-B', str(ROOT / script), *map(str, arguments)]
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        sys.stdout.write(result.stdout)
        sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    print('PASS ' + script, flush=True)
    return result.stdout


def stable(value):
    if isinstance(value, dict):
        return {k: stable(v) for k, v in value.items() if k != 'elapsed_seconds'}
    if isinstance(value, list):
        return [stable(v) for v in value]
    return value


def compare(actual, retained):
    got = json.loads(Path(actual).read_text())
    want = json.loads((ROOT / retained).read_text())
    if stable(got) != stable(want):
        raise AssertionError('Regenerated evidence differs: ' + retained)


def verify_manifest():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        if not path.is_relative_to(ROOT) or '..' in Path(relative).parts:
            raise ValueError('Invalid manifest path')
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise AssertionError('Supplied artifact hash differs: ' + relative)
        count += 1
    print(f'PASS root manifest ({count} files)', flush=True)
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--extended', action='store_true',
                        help='also repeat retained preliminary 26-control and three-map suites')
    arguments = parser.parse_args()
    manifest_count = verify_manifest()
    with tempfile.TemporaryDirectory(prefix='zfc-proof-engine-check-') as temporary:
        out = Path(temporary)
        run('code/verify_name_transport.py', '--output', out / 'name.json')
        compare(out / 'name.json', 'data/name_transport_results.json')
        run('code/verify_integration.py', '--output-dir', out / 'integration')
        for name in ('integration_results.json', 'stream_tables.json',
                     'collision_ui_certificate.json', 'unary_false_instance.json'):
            compare(out / 'integration' / name, 'data/' + name)
        run('shift22/verify_shift_kernel.py', '--output', out / 'shift22.json')
        compare(out / 'shift22.json', 'shift22/shift22_results.json')
        for script, retained in (
                ('code/verify_pair_independent.py', 'data/independent_pair_results.json'),
                ('code/verify_downshift_independent.py', 'data/independent_26_results.json')):
            got = json.loads(run(script))
            if stable(got) != stable(json.loads((ROOT / retained).read_text())):
                raise AssertionError('Independent-check evidence differs: ' + retained)
        if arguments.extended:
            for script, retained in (
                    ('code/verify_transport26.py', 'data/transport26_results.json'),
                    ('code/verify_three_maps.py', 'data/three_maps_results.json')):
                path = out / Path(retained).name
                run(script, '--output', path)
                compare(path, retained)
    run('machine_control/reproduce.py')
    print(json.dumps({'status': 'PASS', 'manifest_files': manifest_count,
                      'extended': arguments.extended,
                      'scope': 'finite reference evidence; no new complete sub-253 machine'},
                     indent=2))


if __name__ == '__main__':
    main()
