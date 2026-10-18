#!/usr/bin/env python3
"""Replay the source-68 245-state package on a disposable copy.

Only the two delivery-checksum-manifest blocks are removed. Exact semantic
machine/source identities and all substantive checks remain unchanged. The
optional literal regression invokes the package's C++17 compiler command;
no Lean/Rocq build or compiler version query is performed by this helper.
"""
from __future__ import annotations

import argparse
import ast
import difflib
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

PATCHES = (
    (
        'code/verify_all.py',
        'a759ce9268ab87a97ae02971ad9aafcf01c86f03d184157d0919db64198c0a5d',
        '''    inventory = ROOT / "SHA256SUMS"
    checked = 0
    for line in inventory.read_text().splitlines():
        expected, rel = line.split("  ", 1)
        path = ROOT / rel
        assert path.is_relative_to(ROOT) and path.is_file(), rel
        assert digest(path) == expected, ("Artifact hash mismatch", rel)
        checked += 1
    print(f"PASS: {checked} delivered file hashes.", flush=True)
''',
        '''    checked = 0
    print("SKIPPED: delivery checksum manifests, per repository intake policy.", flush=True)
''',
    ),
    (
        'code/verify.py',
        '1f3ec760ac980ec5c91be3d896b7fc6282b2d540a7afedd0627ed908f328477d',
        '''    manifest=json.loads((ROOT/'manifest.json').read_text())
    for rel,expected in manifest['sha256'].items():
        assert digest(ROOT/rel)==expected,('Artifact hash mismatch',rel)
''',
        '''    # Delivery checksum manifest intentionally not checked during intake.
''',
    ),
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def save(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + '\n')


def main() -> int:
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled; do not use Python -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', required=True, type=Path,
                        help='Pristine recovered zfc245-proof-20261018 package root.')
    parser.add_argument('--output', required=True, type=Path,
                        help='New external directory; must not already exist.')
    parser.add_argument('--whole-frame', action='store_true')
    parser.add_argument('--literal', action='store_true')
    parser.add_argument('--prepare-only', action='store_true',
                        help='Copy, adapt and record the planned command without executing it.')
    parser.add_argument('--timeout', type=float, default=1200,
                        help='Positive wall-clock bound in seconds for the entire supplied suite.')
    args = parser.parse_args()
    source, out = args.package.resolve(), args.output.resolve()
    if not source.is_dir():
        parser.error('--package must be an existing directory')
    if out.exists():
        parser.error('--output must not already exist')
    if out.is_relative_to(source):
        parser.error('--output must be outside the pristine package')
    if not 0 < args.timeout < float('inf'):
        parser.error('--timeout must be finite and positive')
    paths = sorted(source.rglob('*'))
    if any(p.is_symlink() for p in paths):
        parser.error('The pristine package must contain no symbolic links')
    files = [p for p in paths if p.is_file()]
    for relative, expected, old, new in PATCHES:
        raw = (source / relative).read_bytes()
        if digest(raw) != expected or raw.decode().count(old) != 1:
            parser.error('Unexpected original driver bytes: ' + relative)
    out.mkdir(parents=True, exist_ok=False)
    copy = out / 'package'
    shutil.copytree(source, copy)
    adaptations = []
    for relative, expected, old, new in PATCHES:
        before = (source / relative).read_bytes()
        after = before.decode().replace(old, new).encode()
        ast.parse(after, filename=relative)
        (copy / relative).write_bytes(after)
        adaptations.append(dict(
            path=relative,
            only_change='Skip delivery manifest validation; retain exact semantic input bindings and all substantive checks',
            original_sha256=expected,
            adapted_sha256=digest(after),
            diff=''.join(difflib.unified_diff(
                before.decode().splitlines(True), after.decode().splitlines(True),
                fromfile='delivered/' + relative, tofile='run-copy/' + relative))))
    inventory = []
    changed = []
    for path in files:
        relative = str(path.relative_to(source))
        before, after = path.read_bytes(), (copy / relative).read_bytes()
        if before != after:
            changed.append(relative)
        inventory.append(dict(path=relative, original_sha256=digest(before),
                              copied_sha256=digest(after), size=len(before)))
    assert set(changed) == {entry[0] for entry in PATCHES}
    assert {p.relative_to(copy) for p in copy.rglob('*') if p.is_file()} == {
        p.relative_to(source) for p in files}
    save(out / 'adaptation.json', adaptations)
    save(out / 'package-inventory.json', inventory)
    command = [sys.executable, '-B', str(copy / 'code/verify_all.py'),
               '--output', str(out / 'results')]
    if args.whole_frame:
        command.append('--whole-frame')
    if args.literal:
        command.append('--literal')
    record = dict(
        status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',
        helper_sha256=digest(Path(__file__).read_bytes()),
        original_package=str(source), copied_package=str(copy),
        original_files=len(files), changed_paths=changed,
        adaptation_sha256=digest((out / 'adaptation.json').read_bytes()),
        package_inventory_sha256=digest((out / 'package-inventory.json').read_bytes()),
        delivery_checksum_manifests_checked=False,
        semantic_identity_tests_retained=True,
        whole_frame_requested=args.whole_frame, literal_requested=args.literal,
        timeout_seconds=args.timeout, planned_command=command,
        commands=[], elapsed_seconds=None, returncode=None,
        scope='Executable ordinary mathematical certificates; no new kernel or PA endpoint.',
    )
    save(out / 'replay.json', record)
    if args.prepare_only:
        print(json.dumps(record, indent=2))
        return 0
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    start = time.monotonic()
    log_path = out / 'suite.log'
    record['commands'] = [command]
    save(out / 'replay.json', record)
    child = None
    exit_code = 1
    try:
        with log_path.open('wb') as log:
            child = subprocess.Popen(command, cwd=copy, env=env, stdout=log,
                                     stderr=subprocess.STDOUT, start_new_session=True)
            try:
                returncode = child.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                record['status'] = 'TIMEOUT'
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    child.wait()
                # A terminated leader can leave grandchildren in its group.
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                record['returncode'] = child.returncode
                exit_code = 124
            else:
                record['returncode'] = returncode
                if returncode:
                    record['status'] = 'FAIL'
                    exit_code = returncode if returncode > 0 else 1
                else:
                    summary_path = out / 'results/verification-summary.json'
                    summary = json.loads(summary_path.read_text())
                    assert summary['status'] == 'PASS_245_DELIVERY'
                    assert summary['working_states'] == 245 and summary['binary_rows'] == 490
                    assert summary['delivered_hashes_checked'] == 0
                    assert summary['core']['status'] == 'PASS_245_CERTIFICATE'
                    assert summary['core']['all_affine_cases'] == 8391
                    assert summary['core']['independently_replayed_whole_frame'] == args.whole_frame
                    assert summary['independent_residual_cases'] == 8390
                    assert summary['bootstrap_equations'] == 54
                    assert summary['independent_blank_steps'] == 407915
                    if args.literal:
                        assert summary['literal']['status'] == 'PASS_FINITE_LITERAL_CASES'
                        assert summary['literal']['cases'] == 8385
                        assert summary['literal']['rows_exercised'] == 490
                    else:
                        assert summary['literal'] is None
                    record['status'] = 'PASS'
                    record['summary_sha256'] = digest(summary_path.read_bytes())
                    exit_code = 0
    except BaseException as error:
        record['status'] = 'INTERRUPTED' if isinstance(error, KeyboardInterrupt) else 'ERROR'
        record['error'] = repr(error)
        if child is not None:
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            record['returncode'] = child.returncode
    finally:
        record['elapsed_seconds'] = round(time.monotonic() - start, 6)
        record['exit_code'] = exit_code
        record['logs'] = [dict(path=str(p.relative_to(out)), sha256=digest(p.read_bytes()))
                          for p in sorted(out.rglob('*.log')) if p.is_file()
                          and not p.is_relative_to(copy)]
        save(out / 'replay.json', record)
    print(json.dumps(record, indent=2))
    return exit_code


if __name__ == '__main__':
    raise SystemExit(main())
