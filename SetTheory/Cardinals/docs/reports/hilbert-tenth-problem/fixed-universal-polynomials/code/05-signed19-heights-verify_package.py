#!/usr/bin/env python3
"""Verify the frozen Report 34 payload; optionally rebuild its PDF offline.

This is a byte-integrity and build check, not a mathematical theorem checker.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

MANIFEST_SHA256 = '2ed70b70d4b7aeb5d8164bc223208f88f045be972799e9fba9092c3d6e47aa6c'
ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if condition is not True:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def bad_constant(value):
    raise ValueError('Nonfinite JSON constant: ' + value)


def gate():
    manifest = ROOT / 'MANIFEST.json'
    need(not manifest.is_symlink(), 'Manifest may not be a symlink')
    raw = manifest.read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Enclosing manifest identity mismatch')
    doc = json.loads(raw.decode('utf-8'), object_pairs_hook=unique,
                     parse_constant=bad_constant)
    need(type(doc) is dict and set(doc) == {'schema', 'files'}, 'Manifest shape')
    need(doc['schema'] == 'research-report34-release-v1', 'Manifest schema')
    files = doc['files']
    need(type(files) is dict and len(files) > 0, 'Payload map type')
    for name, record in files.items():
        need(type(name) is str and type(record) is dict and
             set(record) == {'sha256', 'bytes'}, 'Payload entry shape')
        digest, size = record['sha256'], record['bytes']
        need(type(digest) is str and re.fullmatch('[0-9a-f]{64}', digest) is not None,
             'Invalid digest for ' + name)
        need(type(size) is int and size >= 0, 'Invalid byte size for ' + name)
        rel = Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts and
             rel.as_posix() == name, 'Unsafe relative payload path')
        path = ROOT / rel
        need(path.is_file() and not path.is_symlink() and ROOT in path.resolve().parents,
             'Missing or unsafe payload: ' + name)
        data = path.read_bytes()
        need(len(data) == size and sha(data) == digest, 'Payload identity mismatch: ' + name)
    actual = set()
    for path in ROOT.rglob('*'):
        need(not path.is_symlink(), 'Symlink in release inventory')
        if path.is_file():
            actual.add(path.relative_to(ROOT).as_posix())
    need(actual == set(files) | {'MANIFEST.json', 'verify_package.py', 'SHA256SUMS'},
         'Unexpected or missing file in release inventory')
    expected_sums = ''.join(sha((ROOT / name).read_bytes()) + '  ' + name + '\n'
                            for name in sorted(actual - {'SHA256SUMS'}))
    need((ROOT / 'SHA256SUMS').read_text(encoding='utf-8') == expected_sums,
         'Checksum inventory mismatch')
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', metavar='EXTERNAL_DIRECTORY',
                        help='after identity verification, rebuild the PDF outside this release')
    args = parser.parse_args()
    files = gate()
    if args.build:
        destination = Path(args.build).expanduser().resolve()
        need(destination != ROOT and ROOT not in destination.parents,
             'The build directory must be outside the release tree')
        subprocess.run(['sh', str(ROOT / 'build_pdf.sh'), str(destination)],
                       cwd='/', check=True)
        need((destination / 'Research_Report34.pdf').is_file(), 'Build PDF missing')
        need(gate() == files, 'Release changed during build')
    print('PASS: ' + str(len(files)) + ' frozen payload identities' +
          ('; local PDF build completed' if args.build else '') +
          '. This is not a mathematical proof check.')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
