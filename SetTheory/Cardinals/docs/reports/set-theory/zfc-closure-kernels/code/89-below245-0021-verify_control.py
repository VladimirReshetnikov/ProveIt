#!/usr/bin/env python3
"""Replay the new 245-state control, without an optimizer or network.

The inherited verifier's two table identity constants are explicitly
specialized to the delivered control; all its frame equations are unchanged.
No proof-assistant endpoint or sub-245 construction is asserted.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / 'vendor/routing245'
CANONICAL = '7c9d2248deb02566a5cb48cac284fe33ec6f55ad64434c71cc1b628bbb7f55bd'
OLD = '7682e9b337783eb16386f6528d69c0c59d3cb909311d656d8e54824649337b55'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use Python -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--whole-frame', action='store_true')
    ap.add_argument('--output', type=Path, help='A new or empty result directory.')
    args = ap.parse_args()
    started = time.monotonic()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc245-control-'))
    if out.exists() and any(out.iterdir()):
        raise ValueError('The output directory must be empty.')
    out.mkdir(parents=True, exist_ok=True)
    inventory = ROOT / 'SHA256SUMS'
    checked = 0
    if inventory.exists():
        for line in inventory.read_text().splitlines():
            expected, rel = line.split('  ', 1)
            path = (ROOT / rel).resolve()
            assert path.is_relative_to(ROOT) and path.is_file(), rel
            assert digest(path) == expected, ('Changed artifact', rel)
            checked += 1
        print(f'PASS: {checked} artifact hashes.', flush=True)
    else:
        print('Inventory not present: development replay only.', flush=True)
    assert digest(ROOT / 'machine/machine.tm') == CANONICAL
    assert digest(ROOT / 'machine/machine_old.tm') == OLD
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    py = [sys.executable, '-B']

    def run(name, command):
        print(f'Checking {name} ...', flush=True)
        log = out / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f'{name} failed:\n{log.read_text()[-7000:]}')
        print(f'PASS: {name}.', flush=True)

    # The builder records a path relative to its own package.  A temporary
    # candidate underneath that package satisfies this interface without
    # editing any frozen vendor file.  The directory is removed afterward.
    with tempfile.TemporaryDirectory(prefix='_control_replay_', dir=VENDOR) as td:
        candidate = Path(td) / 'grammar.json'
        shutil.copyfile(ROOT / 'grammar.json', candidate)
        run('source-routing-build', py + [VENDOR / 'code/build_routing_machine.py',
            candidate, out / 'built', '--short-scan', '--padding', '64'])
    for name in ('machine.tm', 'machine_old.tm', 'sites_logical.json',
                 'sites_physical.json', 'register_bisimulation.json', 'renumbering.json'):
        assert (out / 'built' / name).read_bytes() == (ROOT / 'machine' / name).read_bytes(), name
    build = json.loads((out / 'built/machine-audit.json').read_text())
    assert build['working_states'] == 245 and build['source_leaves'] == 6460
    assert build['register_program_bisimulation'] == dict(status='PASS', pairs=3013, edges=6024, halt_pairs=1)
    assert build['maximum_zero_run'] == 6 and build['maximum_depth'] == 51

    run('actual-table-macro-affine-boot', py + [VENDOR / 'code/audit_existing_machine.py',
        out / 'built/machine_old.tm', out / 'built/sites_physical.json', out / 'runtime',
        '--padding', '64', '--boot-limit', '500000'])
    runtime = json.loads((out / 'runtime/existing-machine-audit.json').read_text())
    assert runtime['status'] == 'PASS_AFFINE_AND_BOOT'
    assert runtime['macro_inductions']['status'] == 'PASS'
    assert runtime['affine_all_cases']['cases'] == 8391
    assert runtime['blank_boot']['blank_steps'] == 407915

    frame = load('control_frame', VENDOR / 'code/verify_machine_frame245.py')
    frame.CANONICAL_SHA256, frame.OLD_SHA256 = CANONICAL, OLD
    composition = frame.verify(out / 'built', ROOT / 'grammar.json',
                               VENDOR / 'inputs/state_reduction/bootstrap-lock54.txt')
    assert composition['nonhalting_successors_normalized'] == 8390
    assert composition['bootstrap_lock_immediate_projections_checked'] == 54
    (out / 'frame-composition.json').write_text(json.dumps(composition, indent=2) + '\n')

    parameter = load('control_parameter', VENDOR / 'code/check_parameterization.py').check()
    assert parameter['status'] == 'PASS_EXACT_TEXT_EQUALITY'
    (out / 'parameterization.json').write_text(json.dumps(parameter, indent=2) + '\n')
    run('independent-blank', py + [VENDOR / 'code/state_reduction/check_candidate_boot.py',
        '--table', out / 'built/machine_old.tm', '--steps', '407915',
        '--baseline-bootstrap', VENDOR / 'reference/bootstrap/bootstrap.json',
        '--output', out / 'independent-boot.json'])
    boot = json.loads((out / 'independent-boot.json').read_text())
    assert boot['status'] == 'PASS_EXACT_TWO_INTERPRETER_BOOT' and boot['one_count'] == 351

    table, start = frame.table(ROOT / 'machine/machine.tm')
    states = sorted({q for q, _ in table})
    partition = {q: 0 for q in states}
    partition[245] = 1
    while True:
        labels, refined = {}, {}
        for q in states:
            signature = tuple((table[q, b][0], table[q, b][1], partition[table[q, b][2]]) for b in (0, 1))
            refined[q] = labels.setdefault(signature, len(labels))
        refined[245] = len(labels)
        if refined == partition:
            break
        partition = refined
    classes = len({partition[q] for q in states})
    assert classes == 245

    whole = None
    if args.whole_frame:
        run('whole-frame', py + [VENDOR / 'code/full_symbolic_parametric.py',
            '--table', out / 'built/machine_old.tm', '--sites', out / 'built/sites_physical.json',
            '--all-values', '--output', out / 'whole-frame.json'])
        record = json.loads((out / 'whole-frame.json').read_text())
        assert record['status'] == 'PASS' and record['complete'] is True
        assert record['counts']['cases'] == len(record['cases']) == 8391
        assert record['table_sha256'] == OLD and len(record['rows']) == 490
        whole = {k: v for k, v in record.items() if k not in ('cases', 'rows')}
        whole['rows_covered'] = len(record['rows'])
    summary = dict(status='PASS_245_CONTROL', working_states=245, binary_rows=490,
        canonical_sha256=CANONICAL, old_label_sha256=OLD,
        artifact_hashes_checked=checked, source_leaves=6460,
        bisimulation=build['register_program_bisimulation'], affine_cases=8391,
        bootstrap_equations=54, normalized_successors=8390, blank_steps=407915,
        strong_transition_bisimulation_classes=classes, whole_frame=whole,
        seconds=round(time.monotonic() - started, 3), output=str(out),
        proof_status='Ordinary mathematical composition and executable certificates; no new Lean/Rocq or PA endpoint.',
        sub245_machine_found=False)
    (out / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
