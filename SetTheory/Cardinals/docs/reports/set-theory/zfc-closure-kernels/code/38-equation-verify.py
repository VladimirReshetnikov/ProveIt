#!/usr/bin/env python3
"""Replay the packaged finite certificates and tests; optionally rebuild Lean.

Default: source pins, public253 invariant/macro/bootstrap checks and eight
rejection tests, algebraic semantic/certificate tests, and all three independent
RM certificates with six corruption controls. No state/grammar search, compiler
experiment, network fetch, or full upstream Coq build is run. Results go to validation.json.
Use --lean to also run formal/build.py with Lean 4.32.0 selected by ZFC_LEAN or
PATH. Existing historical Lean logs remain distinct from this run's status.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent


def source_pins():
    manifest = json.loads((BASE / 'formal/source_manifest.json').read_text())
    count = 0
    for record in manifest['sources']:
        path = BASE / 'formal/src' / (record['module'].replace('.', '/') + '.lean')
        data = path.read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode('ascii') + b'\0' + data).hexdigest()
        if actual != record['git_blob_sha']:
            raise ValueError('Pinned Lean dependency differs: ' + record['module'])
        count += 1
    return {'status': 'PASS', 'original_lean_dependency_blobs': count,
            'repository': manifest['repository'], 'commit': manifest['commit'],
            'scope': 'Original dependency source identities only; no Lean compilation in this step.'}


def run_step(name, folder, script, timeout):
    command = [sys.executable, '-B', script]
    print(name + ' ...', flush=True)
    begin = time.monotonic()
    env = dict(os.environ)
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    result = {'name': name, 'cwd': folder, 'command': command,
              'portable_command': ['python', '-B', script]}
    try:
        child = subprocess.run(command, cwd=BASE / folder, env=env,
                               capture_output=True, text=True, timeout=timeout)
        result.update(returncode=child.returncode, stdout=child.stdout, stderr=child.stderr,
                      status='PASS' if child.returncode == 0 else 'FAIL')
        if child.stdout.strip():
            try:
                result['structured_output'] = json.loads(child.stdout)
            except json.JSONDecodeError:
                pass
    except subprocess.TimeoutExpired as exc:
        result.update(status='FAIL', returncode=None, error='timeout', timeout_seconds=timeout,
                      stdout=(exc.stdout or b'').decode(errors='replace') if isinstance(exc.stdout, bytes)
                      else (exc.stdout or ''),
                      stderr=(exc.stderr or b'').decode(errors='replace') if isinstance(exc.stderr, bytes)
                      else (exc.stderr or ''))
    except OSError as exc:
        result.update(status='FAIL', returncode=None, error=str(exc))
    result['seconds'] = time.monotonic() - begin
    print('  ' + result['status'] + f" ({result['seconds']:.2f} s)", flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', action='store_true', help='also rebuild the 26-source Lean closure')
    args = parser.parse_args()
    if sys.flags.optimize:
        parser.error('Run without -O: some inherited certificate checks use assertions.')
    if sys.version_info < (3, 10):
        parser.error('Python 3.10 or later is required.')
    started = datetime.now(timezone.utc).isoformat()
    begin = time.monotonic()
    checks = []
    try:
        pinned = source_pins()
        checks.append({'name': 'pinned_lean_source_identities', **pinned})
        print('Pinned Lean source identities: PASS', flush=True)
    except (OSError, ValueError, KeyError) as exc:
        checks.append({'name': 'pinned_lean_source_identities', 'status': 'FAIL', 'error': str(exc)})
        print('Pinned Lean source identities: FAIL', flush=True)
    checks.append(run_step('public253_invariant_macro_and_bootstrap', 'experiments/public253',
                           'check_certificate.py', 180))
    checks.append(run_step('public253_eight_rejection_tests', 'experiments/public253',
                           'test_certificate.py', 180))
    checks.append(run_step('equational_kernel_tests', 'experiments/equational',
                           'test_cyclic_algebra.py', 300))
    checks.append(run_step('grammar_independent_certificates_and_corruption_controls',
                           'experiments/grammar', 'verify_certificates.py', 180))
    if args.lean:
        lean = run_step('fresh_lean_dependency_build', 'formal', 'build.py', 1200)
        record_path = BASE / 'formal/verification.json'
        if lean['status'] == 'PASS':
            record = json.loads(record_path.read_text())
            lean['verification_record'] = record
            if (record.get('status') != 'PASS'
                    or record.get('all_source_modules_recompiled') != 26
                    or 'version 4.32.0' not in record.get('compiler', '')):
                lean['status'] = 'FAIL'
                lean['error'] = 'Expected the full 26-source Lean 4.32.0 build to pass.'
        checks.append(lean)
    status = 'PASS' if all(c['status'] == 'PASS' for c in checks) else 'FAIL'
    result = {'status': status, 'started_at_utc': started,
              'finished_at_utc': datetime.now(timezone.utc).isoformat(),
              'python': sys.version, 'platform': platform.platform(),
              'seconds': time.monotonic() - begin, 'checks': checks,
              'lean_requested': args.lean, 'lean_rebuilt_this_run': args.lean and checks[-1]['status'] == 'PASS',
              'historical_lean_evidence': 'formal/verification.json',
              'searches_rerun': False, 'binary_compiler_experiment_rerun': False,
              'upstream_Coq_rebuilt': False,
              'limitations': [
                  'No state-count record below the attributed public253 machine is established.',
                  'Public253 shortcut checking is an executable finite certificate plus a written induction proof, not a new kernel proof.',
                  'Algebra tests do not replace the general proof; no ZFC-specific ground query or binary compiler is provided.',
                  'Grammar checks establish the supplied relative register-program certificates, not correctness of the binary compiler or a ZFC endpoint.',
                  'The Lean additions characterize model classes and the abstract enumerator, not literal binary simulation or arithmetic internalization.'
              ]}
    (BASE / 'validation.json').write_text(json.dumps(result, indent=2) + '\n')
    print(status + ': validation.json', flush=True)
    return 0 if status == 'PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
