#!/usr/bin/env python3
"""Check the complete package inventory, including strict JSON and path guards.

SHA256SUMS.json detects accidental modification, not malicious replacement of
both files and their manifest. It is deliberately not its own hash entry.
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
CACHE_NAMES = frozenset(('__pycache__', '.pytest_cache', '.mypy_cache',
                         '.ruff_cache', '.cache', '.DS_Store'))


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


def load_json(data):
    """Reject duplicate keys and JavaScript's non-JSON NaN/Infinity constants."""
    return json.loads(data, object_pairs_hook=unique_object,
                      parse_constant=invalid_constant)


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
    """Reject a symlink in any existing directory component, including root."""
    path = Path(path).absolute()
    need('..' not in path.parts, 'unsafe directory path')
    for component in (*reversed(path.parents), path):
        mode = component.lstat().st_mode
        need(stat.S_ISDIR(mode), 'directory is missing, nonregular, or symlinked: '
             + str(component))
    return path


def read_regular(path):
    """Read a regular file without following a final-component symlink."""
    path = Path(path)
    need(stat.S_ISREG(path.lstat().st_mode), 'not a regular file: ' + str(path))
    flags = os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_NONBLOCK', 0)
    fd = os.open(path, flags)
    with os.fdopen(fd, 'rb') as stream:
        need(stat.S_ISREG(os.fstat(stream.fileno()).st_mode),
             'not a regular file: ' + str(path))
        return stream.read()


def scan(root):
    """Return all regular files and directories; reject links and special files."""
    root = check_directory(root)
    files, directories = {}, set()

    def walk(directory):
        with os.scandir(directory) as entries:
            ordered = sorted(entries, key=lambda entry: entry.name)
        for entry in ordered:
            path = Path(entry.path)
            name = path.relative_to(root).as_posix()
            safe_name(name)
            mode = entry.stat(follow_symlinks=False).st_mode
            if stat.S_ISDIR(mode):
                directories.add(name)
                walk(path)
            elif stat.S_ISREG(mode):
                files[name] = path
            else:
                raise ValueError('nonregular package entry: ' + name)
    walk(root)
    return files, directories


def inventory(root):
    files, directories = scan(root)
    found = {name: hashlib.sha256(read_regular(path)).hexdigest()
             for name, path in sorted(files.items()) if name != MANIFEST}
    expected_dirs = {parent.as_posix() for name in found
                     for parent in PurePosixPath(name).parents
                     if parent.as_posix() != '.'}
    need(directories == expected_dirs, 'empty or unexpected package directory')
    return found


def verify(root=ROOT):
    root = check_directory(root)
    manifest = load_json(read_regular(root / MANIFEST).decode('utf-8'))
    need(isinstance(manifest, dict) and bool(manifest),
         'manifest must be a nonempty object')
    for name, digest in manifest.items():
        safe_name(name)
        need(name != MANIFEST, 'manifest must not hash itself')
        need(isinstance(digest, str) and re.fullmatch('[0-9a-f]{64}', digest),
             'invalid SHA-256 digest')
    found = inventory(root)
    need(found == manifest, 'manifest file set or hashes differ')
    return {'status': 'PASS', 'files_checked': len(found)}


def main():
    try:
        print(json.dumps(verify(), sort_keys=True))
    except (ValueError, OSError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, sort_keys=True),
              file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
