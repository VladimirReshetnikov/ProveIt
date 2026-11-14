#!/usr/bin/env python3
"""Replay the released diagnostics with and without Python optimization.

Only the standard library is required. All generated outputs go to a temporary
directory; the release is hash-checked before and after execution. These are
finite implementation diagnostics, not a consistency proof by testing.
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


def require(condition, message):
    if not condition:
        raise ValueError(message)


def verify_hashes():
    manifest = ROOT / 'SHA256SUMS'
    require(manifest.is_file(), 'Missing SHA256SUMS; unpack the complete release.')
    seen = set()
    for line in manifest.read_text(encoding='utf-8').splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), 'Unsafe manifest path')
        require(name not in seen, 'Duplicate manifest entry')
        seen.add(name)
        require(path.is_file(), 'Missing release file: ' + name)
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, 'Hash mismatch: ' + name)
    require(bool(seen), 'Empty release manifest')
    return len(seen)


def run_json(script, arguments, optimized):
    cmd = [sys.executable, '-B'] + (['-O'] if optimized else [])
    cmd += [str(ROOT / 'code' / script), *map(str, arguments)]
    completed = subprocess.run(cmd, cwd=ROOT, text=True,
                               capture_output=True, check=False)
    require(completed.returncode == 0,
            script + ' failed:\n' + completed.stdout[-6000:] + completed.stderr[-6000:])
    return json.loads(completed.stdout)


def saved(name):
    return json.loads((ROOT / 'results' / name).read_text(encoding='utf-8'))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    file_count = verify_hashes()
    if args.verify_only:
        print(json.dumps({'status': 'passed', 'release_files_verified': file_count}))
        return
    jobs = [
        ('emitter', 'frozen_positive_emitter.py', 'frozen_positive_emitter_results.json'),
        ('polynomial', 'frozen_positive_polynomial.py', 'frozen_positive_polynomial_results.json'),
        ('unary', 'unary_diagnostics.py', 'unary_diagnostics_results.json'),
        ('orbit', 'check_unary_orbit_model.py', 'unary_orbit_model_results.json'),
        ('stream', 'positive_stream.py', 'positive_stream_results.json'),
        ('exact_targets', 'replay_certificates.py', 'certificate_replay.json'),
    ]
    baseline = {}
    try:
        with tempfile.TemporaryDirectory(prefix='pa_unary_replay_') as directory:
            temporary = Path(directory)
            for optimized in (False, True):
                mode = 'optimized' if optimized else 'normal'
                for label, script, receipt in jobs:
                    arguments = []
                    cert_path = temporary / (mode + '_certificates.json')
                    if label == 'stream':
                        arguments = ['--check', '--certificates', cert_path]
                    elif label == 'exact_targets':
                        arguments = [ROOT / 'results' / 'positive_certificates.json']
                    result = run_json(script, arguments, optimized)
                    require(result == saved(receipt), mode + ': saved receipt differs for ' + label)
                    if optimized:
                        require(result == baseline[label], '-O changes ' + label)
                    else:
                        baseline[label] = result
                    if label == 'stream':
                        generated = json.loads(cert_path.read_text(encoding='utf-8'))
                        require(generated == saved('positive_certificates.json'),
                                'Generated certificate inventory differs')
                        replay = run_json('replay_certificates.py', [cert_path], optimized)
                        require(replay == saved('certificate_replay.json'),
                                'Independent replay of generated inventory differs')
                    print(mode + ': ' + label + ' passed', file=sys.stderr, flush=True)
                bounded = run_json('positive_stream.py', ['--search', '--limit', '4096'], optimized)
                require(bounded == {'status': 'unknown', 'descriptions_checked': 4096},
                        'Bounded search contract changed')
                print(mode + ': bounded search passed', file=sys.stderr, flush=True)
    finally:
        require(verify_hashes() == file_count, 'Release inventory changed during replay')
    print(json.dumps({
        'status': 'passed',
        'release_files_verified_before_and_after': file_count,
        'modes': ['normal', 'optimized'],
        'diagnostic_suites_per_mode': len(jobs),
        'exact_named_certificate_targets': 16,
        'bounded_search_descriptions_per_mode': 4096,
        'scope': 'Finite diagnostics and exact-target certificate replay; no kernel-checked interpretation or TM-state bound.',
    }, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
