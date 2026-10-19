#!/usr/bin/env python3
"""Replay the frozen contribution offline, without rerunning heuristic search.

Expected failed 244-state experiments are checked as negative controls.  A
PASS for this research package does not assert a machine below 245 states.
All subprocess JSON statuses are checked explicitly in addition to exit codes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parent
VENDOR_SHA = '5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def main():
    if not __debug__:
        raise RuntimeError('Python assertions must be enabled; do not use -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, help='New or empty directory for fresh evidence.')
    ap.add_argument('--full-scanner-audit', action='store_true', help='Repeat the slower expanded scanner premise audit.')
    ap.add_argument('--search', action='store_true', help='Repeat the stated finite C++ elimination searches.')
    ap.add_argument('--whole-frame', action='store_true', help='Repeat the expanded arbitrary-register proof for the new 245-state variant.')
    args = ap.parse_args()
    began = time.monotonic()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-below245-replay-'))
    if out.exists() and any(out.iterdir()):
        ap.error('--output must be new or empty; frozen results will not be overwritten.')
    out.mkdir(parents=True, exist_ok=True)
    logs = out / 'logs'
    logs.mkdir()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    py = [sys.executable, '-B']

    def run(label, command, allowed=(0,)):
        print(label, flush=True)
        with (logs / (label + '.log')).open('w') as log:
            p = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                               stdout=log, stderr=subprocess.STDOUT)
        if p.returncode not in allowed:
            raise RuntimeError(f'{label} exited {p.returncode}; see {logs / (label + ".log")}')
        return p.returncode

    manifest = ROOT / 'SHA256SUMS'
    checked = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            path = (ROOT / name).resolve()
            assert path.is_relative_to(ROOT) and path.is_file()
            assert digest(path) == expected, ('Modified payload', name)
            checked += 1

    vendor = ROOT / 'vendor/zfc245-proof-20261018.zip'
    assert digest(vendor) == VENDOR_SHA
    unpack = out / 'vendor'
    unpack.mkdir()
    with zipfile.ZipFile(vendor) as archive:
        for item in archive.infolist():
            name = PurePosixPath(item.filename)
            assert not name.is_absolute() and '..' not in name.parts
            assert (item.external_attr >> 16) & 0o170000 != 0o120000, 'No symlinks in vendored payload.'
        archive.extractall(unpack)
    reference = unpack / 'zfc245-proof-20261018'

    run('pinned-245-baseline', py + [reference / 'code/verify_all.py', '--output', out / 'baseline'])
    baseline = read(out / 'baseline/verification-summary.json')
    assert baseline['status'] == 'PASS_245_DELIVERY'
    assert baseline['working_states'] == 245 and baseline['delivered_hashes_checked'] == 293

    def build(label, candidate, scanner=6, expected='PASS_SOURCE_AFFINE_AND_BOOT', locks=None, padding=64, frozen=None):
        target = out / label
        command = py + [ROOT / 'code/build_semantic_machine.py', '--reference', reference,
                        '--candidate', candidate, '--output', target,
                        '--scanner-zero-limit', scanner, '--padding', padding, '--boot-limit', 2000000]
        if locks == 54:
            command += ['--require-bootstrap-lock']
        code = run(label, command, allowed=(0,) if expected.startswith('PASS_') else (2,))
        data = read(target / 'semantic-audit.json')
        assert data['status'] == expected
        assert data['exact_ordered_instruction_leaves'] == 6460 and data['route_projections'] == 22
        assert data['source_bisimulation']['status'] == 'PASS'
        assert data['actual_table_macro_inductions']['status'] == 'PASS'
        if locks is not None:
            assert data['bootstrap_lock_equations_passed'] == locks
        if expected == 'PASS_SOURCE_AFFINE_AND_BOOT':
            run(label + '-frame', py + [ROOT / 'code/verify_semantic_frame.py', '--machine', target,
                                        '--output', target / 'frame-composition.json'])
            assert read(target / 'frame-composition.json')['status'] == 'PASS'
        if frozen:
            for name in ('machine.tm', 'machine_old.tm', 'allocation.json', 'renumbering.json',
                         'sites_logical.json', 'sites_physical.json', 'register_bisimulation.json', 'blank_boot.json'):
                assert (target / name).read_bytes() == (ROOT / frozen / name).read_bytes(), (label, 'Frozen certificate differs', name)
        return data

    control = build('canonical-control', ROOT / 'inputs/canonical-baseline.json', locks=54, frozen='machines/canonical-control245')
    assert control['working_states'] == 245 and control['blank_boot']['blank_steps'] == 407915
    sys.path.insert(0, str(ROOT / 'code'))
    from build_semantic_machine import load_model
    from verify_semantic_frame import table
    *_, encode, finest, code = load_model(reference)
    old, _ = table(reference / 'machine/zfc245_old.tm')
    fresh, _ = table(out / 'canonical-control/machine_old.tm')
    original_alloc = read(out / 'baseline/core/built/allocation.json')
    new_alloc = read(out / 'canonical-control/allocation.json')
    remap = {q: q for q, bit in old}
    remap[254] = 254
    for word, state in original_alloc.items():
        remap[state] = new_alloc[encode(word)]
    assert len(set(remap.values())) == len(remap)
    assert {(remap[q], b): (w, d, remap[t]) for (q, b), (w, d, t) in old.items()} == fresh
    relabel = dict(status='PASS_EXACT_TABLE_RELABELING', rows=len(old), working_states=245,
                   mapping=remap, original_sha256=digest(reference / 'machine/zfc245_old.tm'),
                   new_sha256=digest(out / 'canonical-control/machine_old.tm'))
    (out / 'canonical-control-renumbering.json').write_text(json.dumps(relabel, indent=2) + '\n')

    relaxed = build('relaxed50-245', ROOT / 'inputs/relax50-seed.json', locks=50, frozen='machines/relaxed50-245')
    assert relaxed['working_states'] == 245 and relaxed['blank_boot']['blank_steps'] == 407995
    assert relaxed['source_bisimulation']['pairs'] == 3016
    assert relaxed['affine_all_cases']['cases'] == 8391
    assert relaxed['blank_boot']['all_one_positions'] == control['blank_boot']['all_one_positions']

    failed = build('negative244-relaxed50', ROOT / 'inputs/relax50-seed.json', scanner=5,
                   expected='NOT_A_VERIFIED_COMPLETE_MACHINE', locks=50, frozen='experiments/rejected244-relaxed50')
    assert failed['working_states'] == 244 and failed['affine_all_cases']['status'] == 'FAIL'
    assert failed['affine_all_cases']['first_bad_case']['pc'] == '11101001001000000'
    assert failed['blank_boot']['status'] == 'PASS' and failed['blank_boot']['blank_steps'] == 405175

    witness = build('zero5-witness252', ROOT / 'inputs/zero5-final.json', scanner=5, padding=96,
                    locks=50, frozen='machines/zero5-witness252')
    assert witness['working_states'] == 252 and witness['grammar_rules'] == 136
    assert witness['maximum_zero_run'] == 5 and witness['maximum_depth'] == 61
    assert witness['blank_boot']['blank_steps'] == 405175
    assert witness['affine_all_cases']['cases'] == 8391

    run('zero5-lock-obstruction', py + [ROOT / 'research/grammar/verify_zero5_bootstrap_obstruction.py',
                                        '--package', reference, '--output', out / 'zero5-lock-obstruction.json'])
    obstruction = read(out / 'zero5-lock-obstruction.json')
    run('abstract-grammar-checks', py + [ROOT / 'research/grammar/verify.py', '--output', out / 'grammar'])
    grammar_checks = read(out / 'grammar/grammar-verification.json')
    assert grammar_checks['status'] == 'PASS_FINITE_GRAMMAR_RESEARCH'
    assert len(grammar_checks['candidate_checks']) == 11

    framework_args = py + [ROOT / 'research/framework/verify.py', '--reference', reference,
                           '--output', out / 'framework']
    if args.full_scanner_audit:
        framework_args += ['--full-scanner-audit']
    if args.search:
        framework_args += ['--search']
    run('framework-controls', framework_args)
    assert read(out / 'framework/verification.json')['status'] == 'PASS_RESEARCH_VERIFICATION'
    run('theory-codec-controls', py + [ROOT / 'research/theory/verify.py', '--output', out / 'theory'])
    assert read(out / 'theory/verification.json')['status'] == 'PASS'

    expanded = None
    if args.whole_frame:
        target = out / 'relaxed50-245'
        run('relaxed50-expanded-frame', py + [reference / 'code/full_symbolic_parametric.py',
            '--table', target / 'machine_old.tm', '--sites', target / 'sites_physical.json',
            '--all-values', '--output', out / 'expanded-frame.json'])
        expanded = read(out / 'expanded-frame.json')
        assert expanded['status'] == 'PASS' and expanded['complete']

    result = dict(status='PASS_RESEARCH_PACKAGE_NO_SUB245_CLAIM',
                  payload_hashes_checked=checked, vendor_archive_sha256=VENDOR_SHA,
                  best_verified_working_states=245, requested_sub245_endpoint_achieved=False,
                  baseline_boot_steps=407915, relaxed50_boot_steps=407995,
                  relaxed50_all_parameter_cases=8391,
                  rejected244_runtime_case='11101001001000000',
                  rejected244_blank_steps=405175, zero5_obstruction=obstruction,
                  working_shorter_scanner_states=252, working_shorter_scanner_grammar_rules=136,
                  expanded_frame=expanded, finite_search_repeated=args.search,
                  full_scanner_audit_repeated=args.full_scanner_audit,
                  elapsed_seconds=round(time.monotonic() - began, 3), output=str(out),
                  proof_scope='Ordinary mathematical and executable certificates; no new proof-assistant endpoint.')
    (out / 'verification-summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'zero5_obstruction'}, indent=2))


if __name__ == '__main__':
    main()
