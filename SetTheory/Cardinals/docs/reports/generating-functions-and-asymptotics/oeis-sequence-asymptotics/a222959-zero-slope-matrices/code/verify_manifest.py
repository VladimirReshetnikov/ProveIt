#!/usr/bin/env python3
"""Validate the closed Report194 release inventory, sizes, and SHA-256 hashes.

The manifest detects modification, not replacement of both files and manifest.
This command performs no network access and never changes the package.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
MANIFEST = 'SHA256SUMS.json'
SCHEMA = 'report194-manifest-v1'
MAX_FILE_BYTES = 8 * 1024 * 1024
MAX_TOTAL_BYTES = 32 * 1024 * 1024
MAX_MANIFEST_BYTES = 64 * 1024
CACHE_NAMES = frozenset(('__pycache__', '.pytest_cache', '.mypy_cache',
                         '.ruff_cache', '.cache', '.DS_Store'))
# Sole source allowlist. There are no globbed or recursively admitted inputs.
SOURCES = (
    'Report194.tex', 'README.md', 'README_REPRODUCIBILITY.md', 'DATA_SOURCES.md',
    'build.py', 'test_build.py', 'verify_manifest.py', 'reproduce.py',
    'code/check_exact.py', 'code/matrix_exact.py', 'code/README.md', 'code/PROVENANCE.json',
    'code/derive_second_correction.py', 'code/verify_second_correction.py',
    'data/reference.json', 'data/README.md',
)
GENERATED = ('Report194.pdf', 'generated/exact_checks.json',
             'generated/verification.json', 'generated/build_guards.json',
             'generated/BUILD_INFO.json')

RELEASE_FILES = SOURCES + GENERATED


def need(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def invalid_constant(value):
    raise ValueError('non-finite JSON constant: ' + value)

def noninteger_number(value):
    raise ValueError('noninteger JSON number is forbidden: ' + value)


def load_json(data):
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_constant=invalid_constant, parse_float=noninteger_number)


def safe_name(name):
    need(isinstance(name, str) and bool(name), 'invalid empty/non-string path')
    need(not any(ord(char) < 32 or ord(char) == 127 for char in name)
         and '\\' not in name and ':' not in name, 'unsafe package path')
    path = PurePosixPath(name)
    need(not path.is_absolute() and path.parts and
         all(part not in ('.', '..') for part in path.parts) and
         path.as_posix() == name, 'unsafe package path')
    need(not any(part in CACHE_NAMES or part.endswith(('.pyc', '.pyo'))
                 for part in path.parts), 'cache files are not permitted')
    return path


def check_directory(path):
    """Reject links and non-directories in every component, including root."""
    path = Path(path).absolute()
    need('..' not in path.parts, 'unsafe directory path')
    for component in (*reversed(path.parents), path):
        need(stat.S_ISDIR(component.lstat().st_mode),
             'directory is missing, nonregular, or symlinked: ' + str(component))
    return path


def read_regular(path, limit=MAX_FILE_BYTES):
    """Read bounded regular data without following any directory or file link."""
    path = Path(path)
    check_directory(path.parent)
    initial = path.lstat()
    need(stat.S_ISREG(initial.st_mode), 'not a regular file: ' + str(path))
    need(initial.st_size <= limit, 'file exceeds size limit: ' + str(path))
    flags = os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_NONBLOCK', 0)
    fd = os.open(path, flags)
    with os.fdopen(fd, 'rb') as stream:
        opened = os.fstat(stream.fileno())
        need(stat.S_ISREG(opened.st_mode) and opened.st_size <= limit,
             'not a bounded regular file: ' + str(path))
        need((initial.st_dev, initial.st_ino) == (opened.st_dev, opened.st_ino),
             'file changed while opening: ' + str(path))
        data = stream.read(limit + 1)
        need(len(data) <= limit and len(data) == opened.st_size,
             'file size changed while reading: ' + str(path))
        return data


def scan(root):
    """Return exact regular-file and directory inventory; reject links/caches."""
    root = check_directory(root)
    files, directories = {}, set()

    def walk(directory):
        with os.scandir(directory) as entries:
            ordered = sorted(entries, key=lambda entry: entry.name)
        for entry in ordered:
            path = Path(entry.path)
            name = path.relative_to(root).as_posix()
            safe_name(name)
            info = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                directories.add(name)
                walk(path)
            elif stat.S_ISREG(info.st_mode):
                need(info.st_size <= MAX_FILE_BYTES, 'file exceeds size limit: ' + name)
                files[name] = path
            else:
                raise ValueError('nonregular package entry: ' + name)
    walk(root)
    return files, directories


def inventory(root):
    files, directories = scan(root)
    found = {}
    for name, path in sorted(files.items()):
        if name == MANIFEST:
            continue
        data = read_regular(path)
        found[name] = {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    need(sum(row['bytes'] for row in found.values()) <= MAX_TOTAL_BYTES,
         'package exceeds total size limit')
    expected_dirs = {parent.as_posix() for name in found
                     for parent in PurePosixPath(name).parents
                     if parent.as_posix() != '.'}
    need(directories == expected_dirs, 'empty or unexpected package directory')
    return found


def document(root):
    return {'schema': SCHEMA, 'report': 194, 'algorithm': 'sha256',
            'files': inventory(root)}


def verify(root=ROOT, expected=None):
    root = check_directory(root)
    data = load_json(read_regular(root / MANIFEST, MAX_MANIFEST_BYTES).decode('utf-8'))
    need(type(data) is dict and set(data) == {'schema', 'report', 'algorithm', 'files'},
         'manifest top-level schema mismatch')
    need(data['schema'] == SCHEMA and type(data['report']) is int
         and data['report'] == 194 and data['algorithm'] == 'sha256',
         'manifest identity mismatch')
    entries = data['files']
    need(type(entries) is dict and bool(entries), 'manifest files must be nonempty object')
    for name, row in entries.items():
        safe_name(name)
        need(name != MANIFEST, 'manifest must not hash itself')
        need(type(row) is dict and set(row) == {'bytes', 'sha256'},
             'manifest file schema mismatch')
        need(type(row['bytes']) is int and 0 <= row['bytes'] <= MAX_FILE_BYTES,
             'invalid byte count')
        need(type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}', row['sha256']),
             'invalid SHA-256 digest')
    names = RELEASE_FILES if expected is None else tuple(expected)
    need(len(names) == len(set(names)), 'duplicate expected file path')
    need(set(entries) == set(names), 'manifest differs from closed release inventory')
    need(sum(row['bytes'] for row in entries.values()) <= MAX_TOTAL_BYTES,
         'manifest exceeds total size limit')
    found = inventory(root)
    need(found == entries, 'manifest file set, sizes, or hashes differ')
    return {'status': 'PASS', 'files_checked': len(found),
            'bytes_checked': sum(row['bytes'] for row in found.values()),
            'schema': SCHEMA}


def main():
    try:
        print(json.dumps(verify(), sort_keys=True))
    except (ValueError, OSError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
