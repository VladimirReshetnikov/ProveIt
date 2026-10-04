#!/usr/bin/env python3
"""Portable read-only adapter for the frozen independently authored audit.

No submitted science code is imported or run. Only the pinned independent
checker is imported, with bytecode writes disabled; its two filesystem globals
are redirected. All writes are confined to a new, disjoint output directory.
"""
import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import sys
import types

MANIFEST_SHA256 = '55c67b5898a6e700d0b4042add71df7e388e55c23fe2f9d73437c76d5be7e76e'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_path(raw, must_exist):
    path = Path(raw)
    require('..' not in path.parts, 'Parent traversal is not allowed in a supplied path')
    path = Path(os.path.abspath(path))
    cursor = Path(path.anchor)
    for part in path.parts[1:]:
        cursor = cursor / part
        try:
            info = cursor.lstat()
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(info.st_mode), 'Symlink path component rejected: ' + str(cursor))
    if must_exist:
        require(path.exists(), 'Required path is missing: ' + str(path))
    return path


def inside(child, parent):
    try:
        child.relative_to(parent)
        return True
    except ValueError:
        return False


def snapshot(root):
    require(root.is_dir(), 'Input root is not a directory: ' + str(root))
    result = {}
    for path in [root, *sorted(root.rglob('*'))]:
        info = path.lstat()
        require(not stat.S_ISLNK(info.st_mode), 'Symlink input rejected: ' + str(path))
        relative = str(path.relative_to(root))
        record = {'mode': info.st_mode, 'mtime_ns': info.st_mtime_ns}
        if stat.S_ISREG(info.st_mode):
            record.update(size=info.st_size, sha256=digest(path))
        else:
            require(stat.S_ISDIR(info.st_mode), 'Nonregular input rejected: ' + str(path))
        result[relative] = record
    return result


def child_file(root, name):
    relative = Path(name)
    require(not relative.is_absolute() and '..' not in relative.parts,
        'Unsafe path in pinned manifest')
    path = checked_path(root / relative, True)
    require(path.is_file(), 'Pinned input is not a file: ' + str(path))
    return path


def main():
    require(sys.flags.optimize == 0 and __debug__,
        'Optimized Python is forbidden: the scientific checker uses assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', required=True, help='Frozen submitted science directory')
    parser.add_argument('--audit-root', required=True, help='Frozen independent audit directory')
    parser.add_argument('--output', required=True, help='New external directory; parent must exist')
    args = parser.parse_args()
    source = checked_path(args.source_root, True)
    audit = checked_path(args.audit_root, True)
    output = checked_path(args.output, False)
    require(source.is_dir() and audit.is_dir(), 'Both input roots must be directories')
    for root in [source, audit]:
        require(not inside(output, root) and not inside(root, output),
            'Output must not overlap either frozen input root')
    require(not output.exists(), 'Output already exists; a fresh directory is required')
    require(output.parent.is_dir(), 'Output parent directory must already exist')
    before = {'science': snapshot(source), 'audit': snapshot(audit)}
    manifest_file = child_file(audit, 'audit-manifest.json')
    require(digest(manifest_file) == MANIFEST_SHA256, 'Frozen audit manifest hash mismatch')
    manifest = json.loads(manifest_file.read_text())
    for group, root in [('submitted_files', source), ('audit_files', audit)]:
        for name, expected in manifest[group].items():
            path = child_file(root, name)
            require(path.stat().st_size == expected['bytes'] and digest(path) == expected['sha256'],
                'Frozen input pin mismatch: ' + group + '/' + name)
    checker = child_file(audit, 'independent_check.py')
    expected_receipt = child_file(audit, 'audit-receipt.json').read_bytes()
    expected_log = child_file(audit, 'audit-run.log').read_bytes()
    output.mkdir(mode=0o700)
    try:
        shutil.copyfile(child_file(audit, 'pell-pinned-fetch.json'), output / 'pell-pinned-fetch.json')
        old_bytecode = sys.dont_write_bytecode
        sys.dont_write_bytecode = True
        try:
            module = types.ModuleType('frozen_independent_sandpile_audit')
            module.__file__ = str(checker)
            # Compile the authenticated source bytes directly, so an unlisted
            # pre-existing pyc cannot substitute for the pinned independent code.
            # Submitted executable files remain inert data throughout.
            code = compile(checker.read_bytes(), str(checker), 'exec', dont_inherit=True, optimize=0)
            exec(code, module.__dict__)
            module.SUBMITTED = source
            module.HERE = output
            with (output / 'audit-run.log').open('w') as log, contextlib.redirect_stdout(log):
                module.main()
        finally:
            sys.dont_write_bytecode = old_bytecode
        require((output / 'audit-receipt.json').read_bytes() == expected_receipt,
            'Replayed scientific receipt differs from the frozen receipt')
        require((output / 'audit-run.log').read_bytes() == expected_log,
            'Replayed scientific log differs from the frozen log')
    finally:
        after = {'science': snapshot(source), 'audit': snapshot(audit)}
        require(before == after, 'Frozen input bytes, modes, mtimes, or tree changed during replay')
    result = {
        'status': 'PASS',
        'adapter_kind': 'Two path globals only; frozen checker bytes unchanged',
        'audit_manifest_sha256': MANIFEST_SHA256,
        'checker_sha256': digest(checker),
        'scientific_receipt_sha256': digest(output / 'audit-receipt.json'),
        'scientific_log_sha256': digest(output / 'audit-run.log'),
        'runner_sha256': digest(Path(__file__)),
        'receipt_byte_identical': True,
        'log_byte_identical': True,
        'source_bytes_modes_mtimes_and_tree_preserved': True,
        'submitted_executable_files_run': False,
        'optimized_python_rejected': True,
    }
    (output / 'replay-receipt.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('Replay refused or failed: ' + str(error), file=sys.stderr)
        sys.exit(1)
