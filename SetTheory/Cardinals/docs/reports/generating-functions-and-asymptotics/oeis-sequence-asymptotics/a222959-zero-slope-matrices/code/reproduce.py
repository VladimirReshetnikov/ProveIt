#!/usr/bin/env python3
"""Replay the integer/Fraction checks in normal and optimized isolated Python.

No TeX, floating diagnostics, third-party modules, or network are required.
All durable output is written to a fresh directory outside the source tree.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
import verify_manifest as manifest


def need(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n').encode('utf-8')


def snapshot(root):
    files, directories = manifest.scan(root)
    return ({name: hashlib.sha256(manifest.read_regular(path)).hexdigest()
             for name, path in sorted(files.items())}, directories)


def checked_output(root, output):
    output = Path(output).absolute()
    need('..' not in output.parts, 'unsafe reproduction output')
    manifest.check_directory(output.parent)
    need(not os.path.lexists(output), 'reproduction output already exists')
    need(not output.resolve().is_relative_to(root.resolve()), 'output must be outside package')
    return output


def run_script(root, output, optimized):
    command = [sys.executable, '-I', '-S', '-B'] + (['-O'] if optimized else [])
    command += [str(root / 'code/check_exact.py'), '--output', str(output)]
    env = {'PATH': os.defpath, 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
           'PYTHONHASHSEED': '0', 'PYTHONDONTWRITEBYTECODE': '1', 'TZ': 'UTC'}
    completed = subprocess.run(command, cwd=root, env=env, capture_output=True,
                               timeout=900, shell=False)
    need(completed.returncode == 0, 'exact checker failed:\n' +
         (completed.stdout + completed.stderr)[-12000:].decode('utf-8', errors='replace'))
    data = manifest.read_regular(output)
    parsed = manifest.load_json(data.decode('utf-8'))
    need(type(parsed) is dict and parsed.get('status') == 'passed',
         'exact checker must return a passed object')
    need(parsed.get('arithmetic') == 'integer and Fraction only',
         'exact checker arithmetic declaration mismatch')
    need(completed.stdout == data, 'exact checker stdout differs from its output file')
    return data


def run(root, output):
    root = manifest.check_directory(root)
    output = checked_output(root, output)
    # Lazy import avoids a module cycle and applies the same closed inventory as build.
    import build
    build.validate_source(root)
    before = snapshot(root)
    with tempfile.TemporaryDirectory(prefix='report194-replay-', dir=output.parent) as temporary:
        work = Path(temporary)
        values = []
        for mode, optimized in [('normal', False), ('optimized', True)]:
            destination = work / mode
            destination.mkdir()
            values.append(run_script(root, destination / 'exact_checks.json', optimized))
        need(values[0] == values[1], 'normal and optimized exact results differ')
        result = {'status': 'PASS', 'standard_library_only': True,
                  'normal_and_optimized_byte_identical': True,
                  'exact_checks_sha256': hashlib.sha256(values[0]).hexdigest(),
                  'exact_checks_bytes': len(values[0]),
                  'floating_diagnostics_run': False,
                  'scope': 'Exact finite checks; general theorems are proved in Report194'}
        need(snapshot(root) == before, 'source changed during exact replay')
        output.mkdir(exist_ok=False)
        for mode, data in zip(('normal', 'optimized'), values):
            (output / mode).mkdir()
            with (output / mode / 'exact_checks.json').open('xb') as stream:
                stream.write(data)
        with (output / 'RESULT.json').open('xb') as stream:
            stream.write(canonical(result))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path,
                        help='new directory outside package; parent must already exist')
    args = parser.parse_args()
    try:
        if args.output_dir is None:
            with tempfile.TemporaryDirectory(prefix='report194-reproduce-') as temporary:
                result = run(ROOT, Path(temporary) / 'results')
        else:
            result = run(ROOT, args.output_dir)
        print(json.dumps(result, sort_keys=True, indent=2))
    except (ValueError, OSError, TypeError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
