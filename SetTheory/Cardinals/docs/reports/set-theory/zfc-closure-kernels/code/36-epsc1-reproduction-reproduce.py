#!/usr/bin/env python3
"""Reproduce the report's finite results from included inputs, without network.

Default: model diagnostics, exact reachable scanner witness, radius-6 audit,
projection check, prior 268-state certificate, all 432 outgoing-equality builds.
--extended: additionally repeat the 12,002 permutation grammars and the
3,000,000-iteration canonical-substring search (requires a C++17 compiler).

These checks are finite computations, not a Lean/Coq build or a formalized
consistency proof. Run with Python 3.12 and assertions enabled.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
PACKAGE = ROOT.parent
SOURCE = ROOT / 'sources/proveit'
RESEARCH = SOURCE / 'Computability/BusyBeaver/Research/ZFC'
SHA253 = '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
SHA268 = '07b7aa8db8f9fa0440f67db829fad116139409f182a52a3d0a5d92e867247b4a'
SHA290 = '34c49f80aa4e2c14e7ced081cebf8a0867abe1717dde60e78ee432e9b5badde7'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def verify_files():
    # Authenticate the included snapshot independently of ordinary file hashes.
    source = read(ROOT / 'source_manifest.json')
    for name, expected in source['git_blob_sha1'].items():
        data = (SOURCE / name).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert blob == expected, ('source blob', name)
    provenance = read(PACKAGE / 'PROVENANCE.json')
    for entry in provenance['files']:
        assert digest(PACKAGE / entry['path']) == entry['sha256'], entry['path']
    assert digest(ROOT / 'zf_audit/zfc_253.tm') == SHA253
    assert digest(ROOT / 'experiments/baseline268/candidate.tm') == SHA268
    assert digest(ROOT / 'proveit_audit/eout_results/best_complete_proxy.tm') == SHA290
    checksums = PACKAGE / 'CHECKSUMS.sha256'
    if checksums.exists():
        for line in checksums.read_text().splitlines():
            expected, name = line.split('  ', 1)
            assert digest(PACKAGE / name) == expected, ('archive checksum', name)
    return {'source_blobs': len(source['git_blob_sha1']),
            'provenance_files': len(provenance['files'])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--extended', action='store_true')
    parser.add_argument('--verify-only', action='store_true')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Assertions are required: do not use python -O.')
    identities = verify_files()
    print('Verified included file identities:', identities, flush=True)
    if args.verify_only:
        return
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='zfc-report-replay-')))
    output.mkdir(parents=True, exist_ok=True)
    print('Replay output:', output, flush=True)
    steps = []
    environment = os.environ.copy()
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    environment.pop('PYTHONOPTIMIZE', None)

    def run(name, *command):
        start = time.monotonic()
        logfile = output / (name + '.log')
        with logfile.open('w') as log:
            completed = subprocess.run(list(map(str, command)), cwd=ROOT,
                                       env=environment, stdout=log, stderr=subprocess.STDOUT)
        if completed.returncode:
            print(logfile.read_text()[-12000:], file=sys.stderr)
            raise RuntimeError(f'{name} failed; see {logfile}')
        elapsed = time.monotonic() - start
        steps.append({'name': name, 'seconds': elapsed, 'returncode': completed.returncode})
        print(f'{name}: passed ({elapsed:.2f}s)', flush=True)

    py = sys.executable
    run('support', py, ROOT / 'logical_encodings/epsc1_support_diagnostic.py',
        '--output', output / 'epsc1_support_diagnostic.json')
    assert read(output / 'epsc1_support_diagnostic.json') == read(ROOT / 'logical_encodings/epsc1_support_diagnostic.json')
    run('scanner', py, ROOT / 'zf_audit/scanner_boundary.py',
        ROOT / 'zf_audit/zfc_253.tm', ROOT / 'zf_audit/upstream/Prog254.v',
        '--output', output / 'scanner_boundary.json')
    assert read(output / 'scanner_boundary.json') == read(ROOT / 'zf_audit/scanner_boundary.json')
    run('radius6', py, RESEARCH / 'audit_tm.py', ROOT / 'zf_audit/zfc_253.tm',
        '--expected-sha256', SHA253, '--expected-states', 253, '--expected-halt', 253,
        '--source-commit', '0d544f2a2e3c18f12278441a74b7879f31cbe856',
        '--source-url', 'https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm',
        '--window-radius', 6, '--macro-steps', 64, '--self-test',
        '--output', output / 'public253-radius6.json')
    assert read(output / 'public253-radius6.json') == read(ROOT / 'zf_audit/public253-radius6.json')
    run('projection', py, ROOT / 'zf_audit/recompute_windows.py',
        ROOT / 'zf_audit/zfc_253.tm', '--output', output / 'radius6_projection.json')
    actual, prior = read(output / 'radius6_projection.json'), read(ROOT / 'zf_audit/radius6_projection.json')
    actual.pop('elapsed_seconds'); prior.pop('elapsed_seconds')
    assert actual == prior
    run('baseline268', py, RESEARCH / 'layout_grammar_experiment.py',
        '--output', output / 'baseline268', '--start-seed', 130,
        '--seeds', 1, '--exponents', 4, '--lanes', 'coarse')
    assert digest(output / 'baseline268/candidate.tm') == SHA268
    baseline = read(output / 'baseline268/results.json')
    assert baseline['independent_rm_check']['verified']
    assert baseline['independent_rm_check']['pairs'] == 4533
    assert all(x['rejected'] for x in baseline['mutations'])
    run('equality290', py, ROOT / 'proveit_audit/eout_emitter_experiment.py',
        '--repo', SOURCE, '--output', output / 'eout', '--search')
    assert digest(output / 'eout/best_complete_proxy.tm') == SHA290
    equality = read(output / 'eout/evidence.json')
    assert equality['search']['recipes'] == 432 and equality['search']['states'] == 290
    assert equality == read(ROOT / 'proveit_audit/eout_results/evidence.json')

    if args.extended:
        run('permutations', py, ROOT / 'experiments/order_search.py',
            '--output', output / 'permutations')
        actual, prior = read(output / 'permutations/census.json'), read(ROOT / 'experiments/permutations/census.json')
        actual.pop('seconds'); prior.pop('seconds')
        assert actual == prior
        run('rotation_prepare', py, ROOT / 'experiments/prepare_rotation.py',
            '--baseline', output / 'baseline268/grammar.json', '--output', output / 'rotation')
        compiler = shutil.which('g++') or shutil.which('clang++')
        if compiler is None:
            raise RuntimeError('--extended requires g++ or clang++ with C++17 support')
        run('rotation_build', compiler, '-O3', '-std=c++17',
            ROOT / 'experiments/rotate_grammar.cpp', '-o', output / 'rotation/search')
        run('rotation_search', output / 'rotation/search', output / 'rotation/input.txt',
            output / 'rotation/best.txt', 3000000, 20261016)
        run('rotation_check', py, ROOT / 'experiments/check_rotation.py',
            output / 'rotation', output / 'baseline268/grammar.json',
            '--output', output / 'rotation/check.json')
        assert read(output / 'rotation/check.json') == read(ROOT / 'experiments/rotation/check.json')
        assert digest(output / 'rotation/best.txt') == digest(ROOT / 'experiments/rotation/best.txt')

    result = {'status': 'passed', 'extended': args.extended,
              'python': sys.version.split()[0], 'identities': identities,
              'steps': steps,
              'new_sub253_consistency_machine_claimed': False,
              'lean_or_coq_build_run': False}
    (output / 'RUN_RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
    print('All requested finite reproductions passed.', flush=True)


if __name__ == '__main__':
    main()
