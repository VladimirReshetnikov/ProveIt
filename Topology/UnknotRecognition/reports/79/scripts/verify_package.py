#!/usr/bin/env python3
"""Verify every SHA256SUMS record without importing the research runtime.

Use --strict to require that every non-generated package file is recorded.
Python bytecode caches created by running the supplied tests are ignored.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import sys


def digest(path):
    result = sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024*1024), b''):
            result.update(block)
    return result.hexdigest()


def verify(root, strict=False):
    root = Path(root).resolve()
    checksum_file = root/'SHA256SUMS'
    if not checksum_file.is_file():
        raise ValueError('SHA256SUMS is missing')
    expected = {}
    for number, line in enumerate(checksum_file.read_text().splitlines(), 1):
        match = re.fullmatch(r'([0-9a-fA-F]{64}) [ *](.+)', line)
        if match is None:
            raise ValueError('malformed SHA256SUMS line '+str(number))
        checksum, name = match.groups()
        path = PurePosixPath(name)
        if (path.is_absolute() or '\\' in name or '\x00' in name
                or any(part in ('', '.', '..') for part in name.split('/'))
                or name == 'SHA256SUMS' or name in expected):
            raise ValueError('unsafe, duplicate, or self-referential checksum path')
        expected[name] = checksum.lower()
    if not expected:
        raise ValueError('SHA256SUMS contains no file records')
    errors = []
    for name, checksum in expected.items():
        path = root
        for part in PurePosixPath(name).parts:
            path = path/part
            if path.is_symlink():
                errors.append(dict(path=name, reason='symlink is not a package file'))
                break
        else:
            if not path.is_file():
                errors.append(dict(path=name, reason='missing regular file'))
            elif digest(path) != checksum:
                errors.append(dict(path=name, reason='SHA-256 mismatch'))
    actual = set()
    for path in root.rglob('*'):
        relative = path.relative_to(root)
        if '__pycache__' in relative.parts or path.suffix == '.pyc':
            continue
        if path.is_file() and relative.as_posix() != 'SHA256SUMS':
            actual.add(relative.as_posix())
    unlisted = sorted(actual-set(expected))
    if strict and unlisted:
        errors.extend(dict(path=name, reason='file missing from SHA256SUMS') for name in unlisted)
    return dict(status='VERIFIED' if not errors else 'REFUSED',
        package=str(root), strict=strict, checked_files=len(expected),
        unlisted_files=unlisted, errors=errors)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', default=str(Path(__file__).resolve().parents[1]))
    parser.add_argument('--strict', action='store_true')
    arguments = parser.parse_args()
    try:
        result = verify(arguments.root, arguments.strict)
        print(json.dumps(result, indent=2))
        return 0 if result['status'] == 'VERIFIED' else 2
    except (OSError, ValueError) as error:
        print(json.dumps(dict(status='ERROR', reason=str(error)), indent=2))
        return 2


if __name__ == '__main__':
    sys.exit(main())
