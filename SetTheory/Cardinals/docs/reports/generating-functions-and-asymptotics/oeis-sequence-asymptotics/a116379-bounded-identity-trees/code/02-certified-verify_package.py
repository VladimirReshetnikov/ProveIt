#!/usr/bin/env python3
"""Closed-inventory verifier and isolated replay for the Report130 release.

Run with -B to suppress bytecode. This script never writes into the package.
SHA-256 inventory checks establish file identity, not publisher authenticity.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile

MANIFEST = 'SHA256SUMS'

class PackageError(RuntimeError):
    pass

def require(ok, message):
    if not ok:
        raise PackageError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(root):
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'Package root must be a real directory')
    manifest = root / MANIFEST
    require(manifest.is_file() and not manifest.is_symlink(), 'Missing or symlinked manifest')
    raw = manifest.read_bytes()
    require(raw.endswith(b'\n'), 'Manifest must end in a newline')
    try:
        lines = raw.decode('ascii').splitlines()
    except UnicodeDecodeError as exc:
        raise PackageError('Manifest must be ASCII') from exc
    entries = {}
    for line in lines:
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_./-]+)', line)
        require(match is not None, 'Malformed manifest line')
        expected, name = match.groups()
        parts = name.split('/')
        require(not name.startswith('/') and all(p not in ('', '.', '..') for p in parts), 'Unsafe manifest path')
        require(str(PurePosixPath(name)) == name and name != MANIFEST, 'Noncanonical or self-referential manifest path')
        require(name not in entries, 'Duplicate manifest path')
        entries[name] = expected
    require(list(entries) == sorted(entries), 'Manifest paths must be sorted')
    require(bool(entries), 'Empty manifest')
    allowed_dirs = set()
    for name in entries:
        parts = name.split('/')
        allowed_dirs.update('/'.join(parts[:i]) for i in range(1, len(parts)))
    actual = set()
    for path in root.rglob('*'):
        name = path.relative_to(root).as_posix()
        require(not path.is_symlink(), 'Symlinks are forbidden: ' + name)
        if path.is_dir():
            require(name in allowed_dirs, 'Unexpected directory: ' + name)
        else:
            require(path.is_file(), 'Nonregular package entry: ' + name)
            actual.add(name)
    require(actual == set(entries) | {MANIFEST}, 'Inventory mismatch: missing=' + str(sorted((set(entries)|{MANIFEST})-actual)) + '; extra=' + str(sorted(actual-(set(entries)|{MANIFEST}))))
    for name, expected in entries.items():
        require(digest(root/name) == expected, 'Hash mismatch: ' + name)
    return entries

def run_checked(command, cwd, env):
    result = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(result.returncode == 0, 'Command failed: ' + ' '.join(map(str,command)) + '\n' + result.stderr.decode(errors='replace'))
    return result.stdout

def replay(root, build=False):
    root = Path(root).absolute()
    before = inventory(root)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    checks = ['closed_inventory']
    with tempfile.TemporaryDirectory(prefix='report130-replay-') as tmp:
        work = Path(tmp)
        core = root/'certificate'
        for flags, label in (([], 'ordinary_certificate'), (['-O'], 'optimized_certificate')):
            actual = run_checked([sys.executable, '-B', *flags, str(core/'certify.py')], work, env)
            require(actual == (core/'certificate.json').read_bytes(), label + ' differs from reference')
            checks.append(label)
        actual = run_checked([sys.executable, '-B', str(core/'test_certifier.py')], work, env)
        require(actual == (core/'tests.json').read_bytes(), 'Supplementary tests differ from reference')
        checks.append('supplementary_tests')
        exports = work/'exports'; exports.mkdir()
        actual = run_checked([sys.executable, '-B', str(core/'certify.py'), '--coefficients-out', str(exports)], work, env)
        require(actual == (core/'certificate.json').read_bytes(), 'Export run differs from reference')
        for name in ('a_d3_through_400.json', 'a_d4_through_400.json'):
            require((exports/name).read_bytes() == (core/name).read_bytes(), 'Coefficient export mismatch: ' + name)
        snapshot = {p.name:p.read_bytes() for p in exports.iterdir()}
        result = subprocess.run([sys.executable,'-B',str(core/'certify.py'),'--coefficients-out',str(exports)],cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        require(result.returncode != 0 and b'FileExistsError' in result.stderr, 'Existing exports were not rejected')
        require(snapshot == {p.name:p.read_bytes() for p in exports.iterdir()}, 'Rejected export changed files')
        checks += ['coefficient_exports', 'export_overwrite_rejected']
        if build:
            output = work/'pdf'; output.mkdir()
            run_checked(['bash',str(root/'build.sh'),str(output)], work, env)
            require((output/'Report130.pdf').read_bytes() == (root/'Report130.pdf').read_bytes(), 'Rebuilt PDF differs from reference')
            checks.append('byte_identical_pdf_build')
    require(inventory(root) == before, 'Package inventory changed during replay')
    checks.append('source_unchanged')
    return checks

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--replay', action='store_true', help='Replay both Python modes, tests, and safe exports in a temporary directory')
    parser.add_argument('--build', action='store_true', help='Also rebuild and byte-compare the PDF; implies --replay')
    args=parser.parse_args()
    try:
        checks=replay(args.root,args.build) if args.replay or args.build else ['closed_inventory'] if inventory(args.root) else []
    except (PackageError,OSError,ValueError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr)
        return 1
    print(json.dumps({'status':'PASS','checks':checks},indent=2))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
