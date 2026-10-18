#!/usr/bin/env python3
"""Reproduce the exact QT244 construction without a network connection.

Fast replay checks identities, source equivalence, full frame closure, exact
blank initialization, every affine instruction case, and fresh literal cases.
--whole-frame additionally re-proves all instruction paths with explicit
arbitrary registers and an arbitrary nonempty finite spare suffix.
--baseline also executes the unchanged reference package's verification driver.
All generated outputs go to a new directory, leaving delivered files unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = ROOT / 'reference/baseline245'
CANONICAL_SHA = '91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790'
OLD_SHA = '0160caaf5d6db52eb7eb97a76cb04db4b424eb2bc0d58617818a6c7c6a1fe776'
SOURCE_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(root):
    checked = 0
    for line in (root/'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = (root/name).resolve()
        assert path.is_relative_to(root.resolve()) and path.is_file(), name
        assert digest(path) == expected, ('File hash mismatch', name)
        checked += 1
    return checked


def main():
    if not __debug__:
        raise RuntimeError('Assertions are required. Do not use python -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--whole-frame', action='store_true')
    parser.add_argument('--baseline', action='store_true')
    parser.add_argument('--baseline-whole-frame', action='store_true', help='Also repeat the unchanged ancestor expanded proof.')
    parser.add_argument('--output', type=Path, help='A new or empty output directory.')
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='qt244-replay-'))
    if out.exists() and any(out.iterdir()):
        raise ValueError('Output directory must be empty; delivered certificates are never overwritten.')
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    hashes = check_manifest(ROOT)
    baseline_hashes = check_manifest(REFERENCE)
    assert baseline_hashes == 293
    print(f'PASS: {hashes} packet files and {baseline_hashes} baseline files match their manifests.', flush=True)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    py = [sys.executable, '-B']

    def run(name, command):
        print(f'Checking {name} ...', flush=True)
        log = out/(name+'.log')
        with log.open('w') as stream:
            result = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{name} failed:\n{log.read_text()[-12000:]}')
        print(f'PASS: {name}.', flush=True)

    if args.baseline or args.baseline_whole_frame:
        command = py+[REFERENCE/'code/verify_all.py', '--output', out/'baseline']
        if args.baseline_whole_frame:
            command.append('--whole-frame')
        run('reference-construction', command)

    built = out/'built'
    run('construct-table-and-boot', py+[ROOT/'code/make_qt244.py',
        '--reference', REFERENCE, '--output', built])
    for name in ('machine.tm','machine_old.tm','sites_logical.json',
                 'sites_physical.json','renumbering.json','boot.json'):
        assert (built/name).read_bytes() == (ROOT/'machine'/name).read_bytes(), name
    assert digest(built/'machine.tm') == CANONICAL_SHA
    assert digest(built/'machine_old.tm') == OLD_SHA
    assert digest(built/'sites_logical.json') == SOURCE_SHA

    run('independent-source-equivalence', py+[ROOT/'code/check_qt_rotation.py',
        '--reference', REFERENCE, '--output', out/'source'])
    for name in ('sites_logical.json','sites_physical.json'):
        assert (out/'source/right'/name).read_bytes() == (built/name).read_bytes(), name
    source = json.loads((out/'source/right/source_verification.json').read_text())
    assert source['status'] == 'PASS_UNIVERSAL_SOURCE_EQUIVALENCE'
    assert source['context_edges_checked'] == 8385
    assert source['new_guarded_cases'] == 8390

    run('independent-table-and-four-blank-runs', py+[ROOT/'code/check_table_boot.py',
        '--table', built/'machine_old.tm',
        '--baseline', REFERENCE/'certificate/machine_old.tm',
        '--output', out/'independent-blank'])
    boot = json.loads((out/'independent-blank/independent-blank.json').read_text())
    assert boot['blank_steps'] == 407931 and boot['one_count'] == 351
    assert boot['dispatcher'] == 87 and boot['working_states'] == 244

    run('independent-frame-composition', py+[ROOT/'code/check_frames.py',
        '--machine', built, '--output', out/'frame-composition.json'])
    frame = json.loads((out/'frame-composition.json').read_text())
    assert frame['status'] == 'PASS' and frame['nonhalting_successors_normalized'] == 8389

    run('all-universal-affine-instructions', py+[ROOT/'code/check_runtime.py',
        '--reference', REFERENCE, '--candidate', built])
    affine = json.loads((built/'affine-runtime.json').read_text())
    assert affine['complete'] and affine['counts']['cases'] == 8390

    run('independent-finite-literal-instructions', py+[ROOT/'code/check_qt244_literal.py',
        '--candidate', built])
    literal = json.loads((built/'literal-regression.json').read_text())
    assert literal['status'] == 'PASS_FINITE_LITERAL_REGRESSION'
    assert literal['cases'] == 8390 and literal['whole_tape_endpoints_checked']

    expanded = None
    if args.whole_frame:
        run('all-expanded-whole-frame-instructions', py+[ROOT/'code/check_runtime.py',
            '--reference', REFERENCE, '--candidate', built, '--expanded'])
        expanded = json.loads((built/'expanded-runtime.json').read_text())
        assert expanded['status'] == 'PASS_UNIVERSAL_EXPANDED_RUNTIME'
        assert expanded['complete'] and expanded['counts']['cases'] == 8390
        assert expanded['literal_rows_covered'] == 487
        assert expanded['unused_rows'] == [[27,1]]
        assert expanded['table_sha256'] == OLD_SHA
        assert expanded['sites_logical_sha256'] == SOURCE_SHA
    else:
        recorded = json.loads((ROOT/'certificate/expanded-runtime.json').read_text())
        assert recorded['status'] == 'PASS_UNIVERSAL_EXPANDED_RUNTIME'
        assert recorded['complete'] and recorded['counts']['cases'] == 8390
        assert recorded['table_sha256'] == OLD_SHA
        assert recorded['sites_logical_sha256'] == SOURCE_SHA

    proof_folder = out/'logical-alternatives'
    proof_folder.mkdir()
    for name in ('formalism_verify.py','formalism_kbp_proof.txt','formalism_kbpf_proof.txt'):
        shutil.copy2(ROOT/'research/formalisms'/name, proof_folder/name)
    run('independent-logical-certificates', py+[proof_folder/'formalism_verify.py'])

    report = dict(
        status='PASS_244_FULL_REPLAY' if args.whole_frame else 'PASS_244_FAST_REPLAY',
        working_states=244, binary_rows=488, canonical_sha256=CANONICAL_SHA,
        old_label_sha256=OLD_SHA, logical_source_sha256=SOURCE_SHA,
        packet_hashes_checked=hashes, baseline_hashes_checked=baseline_hashes,
        baseline_replayed=args.baseline or args.baseline_whole_frame, baseline_expanded_replayed=args.baseline_whole_frame, expanded_runtime_replayed=args.whole_frame,
        source_context_edges=8385, universal_guarded_cases=8390,
        independently_normalized_nonhalting_successors=8389,
        exact_blank_steps=407931, literal_cases=literal['cases'],
        literal_transitions=literal['literal_steps'],
        runtime_rows_covered=487, retained_unused_row_old_labels=[27,1],
        expanded_symbolic_rules=expanded['counts']['symbolic_rules'] if expanded else None,
        elapsed_seconds=round(time.monotonic()-started,3),
        scope='Ordinary ZFC proof with finite certificates and unbounded induction; no new kernel endpoint.',
        output=str(out))
    (out/'verification-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2),flush=True)


if __name__ == '__main__':
    main()
