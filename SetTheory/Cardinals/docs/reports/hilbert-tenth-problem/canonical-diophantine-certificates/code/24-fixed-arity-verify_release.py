#!/usr/bin/env python3
"""Verify Report50 or replay its independent audit in a fresh external directory.
Authenticate this helper through a trusted external release identity first.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def need(value, message):
    if not value:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        need(key not in out, 'Duplicate JSON key')
        out[key] = value
    return out


def load(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def safe_path(raw, must_exist=False):
    path = Path(raw)
    need('..' not in path.parts, 'Parent traversal is not allowed')
    path = Path(os.path.abspath(path))
    cursor = Path(path.anchor)
    for part in path.parts[1:]:
        cursor = cursor / part
        try:
            info = cursor.lstat()
        except FileNotFoundError:
            continue
        need(not stat.S_ISLNK(info.st_mode), 'Symlink path component rejected')
    if must_exist:
        need(path.exists(), 'Required path missing')
    return path


def inside(child, parent):
    return child == parent or parent in child.parents


def external_new(raw):
    target = safe_path(raw)
    need(not inside(target, ROOT) and not inside(ROOT, target),
        'Output must be disjoint from the entire release')
    need(not target.exists(), 'Output already exists; use a fresh path')
    need(target.parent.is_dir(), 'Output parent must already exist')
    return target


def snapshot(root):
    out = {}
    for path in [root, *sorted(root.rglob('*'))]:
        info = path.lstat()
        regular = stat.S_ISREG(info.st_mode)
        need(regular or stat.S_ISDIR(info.st_mode), 'Nonregular release path')
        out[path.relative_to(root).as_posix()] = (
            sha(path) if regular else None, stat.S_IMODE(info.st_mode), info.st_mtime_ns)
    return out


def authenticate(expected):
    need(type(expected) is str and len(expected) == 64 and
        all(c in '0123456789abcdef' for c in expected), 'Invalid trusted manifest SHA256')
    manifest = safe_path(ROOT / 'MANIFEST.json', True)
    need(manifest.is_file() and sha(manifest) == expected,
        'Manifest does not match trusted digest')
    data = load(manifest)
    need(set(data) == {'schema', 'files'} and data['schema'] == 'report50-inventory-v1'
        and type(data['files']) is dict, 'Invalid manifest schema')
    current = snapshot(ROOT)
    need({name for name, values in current.items() if values[0] is not None} ==
        set(data['files']) | {'MANIFEST.json'}, 'Missing or unexpected release file')
    directories = {'.'}
    for name, entry in data['files'].items():
        relative = PurePosixPath(name)
        need(type(name) is str and not relative.is_absolute() and
            all(part not in ('.', '..') for part in relative.parts) and
            relative.as_posix() == name, 'Unsafe inventory path')
        need(set(entry) == {'sha256', 'bytes', 'mode'} and
            type(entry['bytes']) is int and type(entry['mode']) is int,
            'Invalid inventory entry')
        path = ROOT / name
        info = path.stat()
        need(sha(path) == entry['sha256'] and info.st_size == entry['bytes'] and
            stat.S_IMODE(info.st_mode) == entry['mode'], 'Inventory mismatch: ' + name)
        directories.update(parent.as_posix() for parent in relative.parents)
    need({name for name, values in current.items() if values[0] is None} == directories,
        'Unexpected directory')
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--verify-only', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    inventory = authenticate(args.manifest_sha256)
    before = snapshot(ROOT)
    result = {'schema': 'report50-release-verification-v1', 'status': 'PASS',
        'manifest_sha256': args.manifest_sha256, 'files': len(inventory['files'])}
    if args.verify_only:
        need(args.output is None, '--verify-only takes no output')
        result['independent_replay_requested'] = False
    else:
        need(sys.flags.optimize == 0 and __debug__, 'Optimized Python is forbidden for replay')
        need(args.output is not None, 'Supply a fresh external --output directory')
        output = external_new(args.output)
        output.mkdir(mode=0o700)
        child = output / 'independent'
        command = [sys.executable, '-I', '-B',
            str(ROOT / 'audit_replay/replay_independent_audit.py'),
            '--source-root', str(ROOT / 'science'),
            '--audit-root', str(ROOT / 'independent_audit'), '--output', str(child)]
        run = subprocess.run(command, cwd=output, capture_output=True, text=True, timeout=600)
        (output / 'runner.stdout').write_text(run.stdout)
        (output / 'runner.stderr').write_text(run.stderr)
        need(run.returncode == 0, 'Independent replay failed: ' + run.stderr[-2000:])
        result.update(independent_replay_requested=True,
            independent=load(child / 'replay-receipt.json'),
            submitted_executable_files_run=False)
    need(snapshot(ROOT) == before, 'Release bytes modes mtimes or tree changed')
    result['release_bytes_modes_mtimes_and_tree_preserved'] = True
    if not args.verify_only:
        (output / 'release-replay-receipt.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
