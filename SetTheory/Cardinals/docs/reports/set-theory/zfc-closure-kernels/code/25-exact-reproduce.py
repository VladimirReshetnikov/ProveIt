#!/usr/bin/env python3
"""Reproduce the report's finite mathematics and portable machine controls.

Requires Python's standard library. Lean checks are optional and explicit.
No network access is used, and generated intermediate files stay in a
temporary directory. This verifies the stated artifacts, not Con(ZFC).
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def run(command, cwd=HERE):
    environment = dict(os.environ)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    environment.pop('PYTHONOPTIMIZE', None)
    result = subprocess.run(list(map(str, command)), cwd=cwd, env=environment,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f'Command failed: {command[0]}\n{result.stdout}\n{result.stderr}')
    return result.stdout


def artifact_integrity():
    path = HERE / 'ARTIFACT_MANIFEST.json'
    if not path.exists():
        return {'status': 'not yet frozen'}
    entries = read_json(path)['files']
    for entry in entries:
        file = HERE / entry['path']
        require(file.is_file(), f'Missing artifact: {entry["path"]}')
        require(file.stat().st_size == entry['bytes'], f'Artifact size mismatch: {entry["path"]}')
        require(hashlib.sha256(file.read_bytes()).hexdigest() == entry['sha256'],
                f'Artifact hash mismatch: {entry["path"]}')
    return {'status': 'PASS', 'files': len(entries)}


def mathematical_checks():
    checked = {}
    for script, stored in [('finite_hulls.py', 'finite_hulls.json'),
                           ('check_reference.py', 'reference_checks.json'),
                           ('wrapper_metrics.py', 'wrapper_metrics.json')]:
        actual = json.loads(run([sys.executable, '-B', HERE / 'code' / script]))
        require(actual == read_json(HERE / 'data' / stored), f'Results differ: {script}')
        checked[script] = {'status': 'PASS', 'recorded_result_matches': True}
    return checked


def lean_checks(executable):
    version = run([executable, '--version']).strip()
    require(re.search(r'\bversion 4\.32\.0(?=[,\s)])', version) is not None,
            f'Expected Lean version 4.32.0; received {version}')
    endpoints = 0
    for name, expected in [('ExactHull', 6), ('ModalBasisAudit', 7)]:
        output = run([executable, f'{name}.lean'], cwd=HERE / 'formal')
        audit = [line for line in output.splitlines() if 'does not depend on any axioms' in line]
        require(len(audit) == expected, f'Unexpected axiom-audit count: {name}')
        require('depends on axioms:' not in output, f'An endpoint has extra axioms: {name}')
        require(output == (HERE / 'data' / f'{name}.check.log').read_text(),
                f'Lean output differs from recorded audit: {name}')
        endpoints += len(audit)
    return {'status': 'PASS', 'version': version, 'empty_axiom_audits': endpoints,
            'scope': 'Explicit local resource and Boolean theorems only.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Run standard checks (the default).')
    parser.add_argument('--full-search', action='store_true', help='Also recompile all 20,480 selected recipes.')
    parser.add_argument('--lean', metavar='EXECUTABLE', help='Also check formal files with the supplied Lean 4.32.0 executable.')
    parser.add_argument('--output', type=Path, help='Optional destination for a complete JSON check report.')
    args = parser.parse_args()
    require(not sys.flags.optimize, 'Do not use python -O for verification')
    begin = time.monotonic()
    report = {'python': sys.version.split()[0], 'offline': True,
              'artifact_integrity': artifact_integrity(),
              'mathematical_checks': mathematical_checks(),
              'new_verified_ConZFC_machine': False}
    with tempfile.TemporaryDirectory(prefix='exact-hull-replay-') as directory:
        output = Path(directory) / 'machine_check.json'
        command = [sys.executable, '-B', HERE / 'machine/reproduce.py', '--quick', '--output', output]
        if args.full_search:
            command.append('--full-search')
        run(command)
        report['machine_checks'] = read_json(output)
    report['lean'] = (lean_checks(args.lean) if args.lean else
                      {'status': 'not requested', 'command': 'python3 reproduce.py --lean lean'})
    report['status'] = 'PASS'
    report['elapsed_seconds'] = time.monotonic() - begin
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': report['status'], 'offline': True,
                      'mathematical_checks': list(report['mathematical_checks']),
                      'controls': [{'mode': row['mode'], 'working_states': row['working_states']}
                                   for row in report['machine_checks']['controls']],
                      'baseline_bootstrap_steps': report['machine_checks']['baseline253']['bootstrap_steps'],
                      'full_compilation_repeated': args.full_search,
                      'lean': report['lean'], 'artifact_integrity': report['artifact_integrity'],
                      'elapsed_seconds': round(report['elapsed_seconds'], 3)}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, RuntimeError, OSError, AssertionError) as error:
        print(f'REPRODUCTION FAIL: {error}', file=sys.stderr)
        raise SystemExit(1)
