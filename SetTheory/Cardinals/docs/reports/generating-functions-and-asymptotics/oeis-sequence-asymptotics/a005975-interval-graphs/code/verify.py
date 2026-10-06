#!/usr/bin/env python3
"""Closed inventory and normal/-O mathematical replay, or deliberate sealing."""
import sys
sys.dont_write_bytecode = True
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import stat
import subprocess
from output_guard import external_output, write_external_bytes

ROOT = Path(__file__).resolve().parent
MANIFEST = 'MANIFEST.sha256'
FILES = tuple(sorted((
    'README.md', 'build-environment.txt', 'build.py', 'check_math.py',
    'output_guard.py', 'pack.py', 'report133.pdf', 'report133.tex',
    'test_adversarial.py', 'verify.py',
)))

class VerificationError(ValueError):
    pass

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def read_regular(path):
    """Reject nonregular files before opening (notably FIFOs), then recheck."""
    require(stat.S_ISREG(path.lstat().st_mode), 'NONREGULAR_FILE: ' + path.name)
    flags = os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_NONBLOCK', 0)
    fd = os.open(path, flags)
    with os.fdopen(fd, 'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode),
                'NONREGULAR_FILE: ' + path.name)
        return stream.read()

def inventory(root=ROOT, *, author_unsealed=False, sealing=False):
    """A flat bundle: no directory, symlink or special file is acceptable."""
    root = Path(root)
    require(stat.S_ISDIR(root.lstat().st_mode), 'BUNDLE_ROOT_NOT_REAL_DIRECTORY')
    names = set()
    for entry in root.iterdir():
        mode = entry.lstat().st_mode
        require(not stat.S_ISLNK(mode), 'SYMLINK: ' + entry.name)
        require(not stat.S_ISDIR(mode), 'DIRECTORY: ' + entry.name)
        require(stat.S_ISREG(mode), 'NONREGULAR_FILE: ' + entry.name)
        names.add(entry.name)
    expected = set(FILES) | {MANIFEST}
    optional = {'report133.pdf', MANIFEST} if author_unsealed else ({MANIFEST} if sealing else set())
    require(not (names - expected), 'UNEXPECTED_FILE: ' + ', '.join(sorted(names - expected)))
    require(not (expected - names - optional),
            'MISSING_FILE: ' + ', '.join(sorted(expected - names - optional)))
    blobs = {name: read_regular(root / name) for name in sorted(names)}
    if author_unsealed:
        require(MANIFEST not in names, 'AUTHOR_MODE_REQUIRES_ABSENT_MANIFEST')
    return blobs

def manifest_bytes(blobs):
    return ''.join(sha256(blobs[name]).hexdigest() + '  ' + name + '\n'
                   for name in FILES).encode('ascii')

def check_inventory(root=ROOT):
    blobs = inventory(root)
    raw = blobs[MANIFEST]
    try:
        lines = raw.decode('ascii').splitlines(keepends=True)
    except UnicodeError as exc:
        raise VerificationError('MANIFEST_NOT_ASCII') from exc
    parsed = []
    for line in lines:
        match = re.fullmatch(r'([0-9a-f]{64})  ([A-Za-z0-9_.-]+)\n', line)
        require(match is not None, 'MALFORMED_MANIFEST_LINE')
        digest, name = match.groups()
        parsed.append((name, digest))
    require(tuple(name for name, _ in parsed) == FILES, 'MANIFEST_CLOSED_INVENTORY_MISMATCH')
    changed = [name for name, digest in parsed if sha256(blobs[name]).hexdigest() != digest]
    require(not changed, 'HASH_MISMATCH: ' + ', '.join(changed))
    require(raw == manifest_bytes(blobs), 'NONCANONICAL_MANIFEST')
    return blobs

def run_math(root=ROOT):
    outputs = []
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env['PYTHONHASHSEED'] = '0'
    for optimized in (False, True):
        command = [sys.executable, '-B'] + (['-O'] if optimized else []) + [str(Path(root) / 'check_math.py')]
        result = subprocess.run(command, cwd=root, env=env, capture_output=True, timeout=240)
        require(result.returncode == 0, ('OPTIMIZED' if optimized else 'NORMAL') +
                '_MATH_FAILED: ' + (result.stdout + result.stderr).decode(errors='replace')[-8000:])
        require(not result.stderr, 'MATH_STDERR_NOT_EMPTY')
        try:
            decoded = json.loads(result.stdout)
        except (UnicodeError, ValueError) as exc:
            raise VerificationError('MATH_OUTPUT_NOT_JSON') from exc
        require(isinstance(decoded, dict) and decoded.get('status') == 'PASS', 'MATH_STATUS_NOT_PASS')
        outputs.append(result.stdout)
    require(outputs[0] == outputs[1], 'NORMAL_OPTIMIZED_MATH_BYTES_DIFFER')
    return {'normal_optimized_bytes_equal': True,
            'output_sha256': sha256(outputs[0]).hexdigest(),
            'results': json.loads(outputs[0])}

def verify(root=ROOT, *, inventory_only=False):
    before = check_inventory(root)
    result = {'status': 'PASS', 'hashed_files': len(FILES), 'manifest_sha256': sha256(before[MANIFEST]).hexdigest()}
    if not inventory_only:
        result['mathematics'] = run_math(root)
    require(check_inventory(root) == before, 'BUNDLE_CHANGED_DURING_VERIFICATION')
    return result

def seal(root=ROOT):
    """Author-only exception: exclusively create the previously absent seal."""
    root = Path(root)
    destination = root / MANIFEST
    require(not os.path.lexists(destination), 'SEAL_ALREADY_EXISTS')
    blobs = inventory(root, sealing=True)
    require(set(blobs) == set(FILES), 'SEAL_REQUIRES_COMPLETE_BUNDLE')
    with destination.open('xb') as stream:
        stream.write(manifest_bytes(blobs))
    check_inventory(root)
    return {'status': 'SEALED', 'hashed_files': len(FILES),
            'manifest_sha256': sha256(destination.read_bytes()).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='new external JSON file; otherwise stdout only')
    parser.add_argument('--inventory-only', action='store_true', help='skip mathematical replay explicitly')
    parser.add_argument('--seal', action='store_true', help='author-only: create absent MANIFEST.sha256')
    args = parser.parse_args()
    try:
        if args.seal:
            require(args.output is None and not args.inventory_only, 'SEAL_OPTIONS_CONFLICT')
            result = seal()
        else:
            if args.output is not None:
                external_output(args.output, ROOT)  # Before inventory reads or mathematical work.
            result = verify(inventory_only=args.inventory_only)
        data = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
        if args.output is not None:
            write_external_bytes(args.output, data, ROOT)
        sys.stdout.buffer.write(data)
    except (ValueError, OSError, subprocess.SubprocessError) as exc:
        print('VERIFY_FAIL: ' + str(exc), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
