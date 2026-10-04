#!/usr/bin/env python3
"""Owned Report61 release operations only: prepare editable TeX; seal files and ZIP.
No scientific source, checker, schedule, constructor, or upstream executable runs.
Use python3 -I -S -B tools/release61.py prepare
Use python3 -I -S -B tools/release61.py seal --zip /fresh/external/name.zip
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import re
import tempfile
import sys
import zipfile

ROOT = Path(__file__).absolute().parent.parent
MODULES = ('Report61.tex', 'results.tex', 'geometry.tex', 'reversal.tex', 'realization.tex', 'evidence.tex')
SCIENCE_PINS = {
    'science/frozen-proof/PROOF.md': 'dc97e30c56817370138d6be760d44a5df031743a0ee1011cca39381b67bb0cec',
    'science/frozen-proof/MANIFEST.json': '715bbbc817188a1a4d90ea7ad673fe4c69a9df105e202828c1835ae308e6f7eb',
    'science/frozen-proof/dependencies/POSITIVE_COMPILER_PROOF.md': 'e0ddd64cdbbb5c7f448266ab58f1dfeb2868892ac0f230632b2337e4d0bed065',
    'audits/scientific/MANIFEST.json': 'dbbc49723fad5b5ab34cd8dab1b8824d66d22b50e384d948e1de0576b7e16aef',
}

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()

def read(path):
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1, 'Not a single-link regular file: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as f:
        opened = os.fstat(f.fileno())
        data = f.read()
        after = os.fstat(f.fileno())
    final = path.lstat()
    def sig(s):
        return (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(sig(before) == sig(opened) == sig(after) == sig(final), 'Concurrent input change')
    return data

def check_root():
    snapshot = full_inventory()
    check_frozen(snapshot)
    return snapshot

def new_external(raw):
    p = Path(raw)
    require(raw.startswith('/') and not raw.startswith('//') and str(p) == raw, 'Canonical absolute output path required')
    require('..' not in p.parts and '.' not in p.parts, 'Output path alias')
    require(not os.path.lexists(p), 'Output already exists')
    require(p.parent == p.parent.resolve(strict=True), 'Output parent is not canonical')
    require(ROOT not in p.parents and p not in ROOT.parents, 'Output must be external to release')
    return p

def prepare():
    require(not (ROOT / 'RELEASE_MANIFEST.json').exists(), 'Cannot prepare a sealed release')
    require(set(p.name for p in (ROOT / 'manuscript').iterdir()) <= set(MODULES) | {'MANUSCRIPT_PINS.json'}, 'Unexpected manuscript entries')
    before = full_inventory()
    sources = {name: read(ROOT / 'manuscript' / name) for name in MODULES}
    flat = sources['Report61.tex']
    for name in MODULES[1:]:
        token = ('\\input{' + name + '}\n').encode()
        require(flat.count(token) == 1, 'Expected one module input: ' + name)
        flat = flat.replace(token, sources[name])
    require(re.search(rb'\\(?:input|include)\b', flat) is None, 'Unexpanded manuscript input')
    pins = {name: {'bytes': len(data), 'sha256': sha(data)} for name, data in sources.items()}
    for name, data in [('Report61.tex', flat), ('manuscript/MANUSCRIPT_PINS.json', encoded(pins))]:
        path = ROOT / name
        if os.path.lexists(path):
            read(path)
        flags = os.O_WRONLY | os.O_NOFOLLOW | (os.O_TRUNC if path.exists() else os.O_CREAT | os.O_EXCL)
        with os.fdopen(os.open(path, flags, 0o644), 'wb') as f:
            f.write(data)
    after = full_inventory()
    ignored = {'Report61.tex', 'manuscript/MANUSCRIPT_PINS.json'}
    require({n: r for n, r in before['files'].items() if n not in ignored} == {n: r for n, r in after['files'].items() if n not in ignored} and before['directories'] == after['directories'], 'Unrelated source changed during preparation')
    print(encoded({'standalone_sha256': sha(flat), 'pins_sha256': sha(encoded(pins))}).decode(), end='')

def seal(zip_path):
    require((ROOT / 'Report61.pdf').is_file(), 'Final PDF missing')
    require((ROOT / 'qa' / 'VISUAL_REVIEW.md').is_file(), 'Visual review record missing')
    dest = new_external(zip_path)
    before = full_inventory()
    expected_dirs = {str(parent) for name in before['files'] for parent in Path(name).parents if str(parent) != '.'}
    require(set(before['directories']) == expected_dirs, 'Unexpected empty release directory at seal')
    records = {}
    payload = {}
    for path in sorted(ROOT.rglob('*')):
        if path.is_file() and path != ROOT / 'RELEASE_MANIFEST.json':
            name = path.relative_to(ROOT).as_posix()
            data = read(path)
            records[name] = {'sha256': sha(data), 'bytes': len(data)}
            payload[name] = data
    manifest = encoded({'report': 61, 'format': 1, 'scope': 'Every regular release file except this manifest; ZIP separately hashed', 'files': records})
    manifest_path = ROOT / 'RELEASE_MANIFEST.json'
    if os.path.lexists(manifest_path):
        require(read(manifest_path) == manifest, 'Existing release manifest is stale')
    else:
        with manifest_path.open('xb') as stream:
            stream.write(manifest)
    payload['RELEASE_MANIFEST.json'] = manifest
    with zipfile.ZipFile(dest, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(payload.items()):
            item = zipfile.ZipInfo('Report61/' + name, date_time=(2026, 10, 4, 0, 0, 0))
            item.create_system = 3
            item.external_attr = (stat.S_IFREG | 0o644) << 16
            item.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(item, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    with zipfile.ZipFile(dest) as archive:
        require(archive.namelist() == ['Report61/' + n for n in sorted(payload)], 'ZIP member inventory mismatch')
        require(archive.testzip() is None, 'ZIP CRC failure')
        for name, data in payload.items():
            require(archive.read('Report61/' + name) == data, 'ZIP payload mismatch')
        with tempfile.TemporaryDirectory(prefix='report61-roundtrip-', dir='/tmp') as temp:
            archive.extractall(temp)
            extracted = Path(temp) / 'Report61'
            actual = {p.relative_to(extracted).as_posix(): read(p) for p in extracted.rglob('*') if p.is_file()}
            require(actual == payload, 'ZIP extraction roundtrip mismatch')
    for name, data in payload.items():
        require(read(ROOT / name) == data, 'Release changed while sealing')
    after = full_inventory()
    require({n: r for n, r in before['files'].items() if n != 'RELEASE_MANIFEST.json'} == {n: r for n, r in after['files'].items() if n != 'RELEASE_MANIFEST.json'} and before['directories'] == after['directories'], 'Release changed while sealing')
    check_manifest(sha(manifest))
    print(encoded({'manifest_sha256': sha(manifest), 'zip': str(dest), 'zip_sha256': sha(read(dest)), 'members': len(payload)}).decode(), end='')


INPUT_PINS_SHA256 = 'acfe4a9a7ac4247b29203c28af9e9907d5e05cfea1e454ac65a846b2221e8c45'

def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key')
        result[key] = value
    return result

def parse(data):
    def bad_constant(value):
        raise ValueError('Nonfinite JSON value')
    return json.loads(data, object_pairs_hook=unique_object, parse_constant=bad_constant)

def row_valid(row):
    return isinstance(row, dict) and set(row) == {'bytes', 'sha256'} and type(row['bytes']) is int and row['bytes'] >= 0 and isinstance(row['sha256'], str) and re.fullmatch(r'[0-9a-f]{64}', row['sha256']) is not None

def safe_name(name):
    return isinstance(name, str) and name and all(re.fullmatch(r'[A-Za-z0-9_.-]+', part) and part not in ('.', '..') for part in name.split('/'))

def full_inventory():
    require(ROOT == ROOT.resolve(strict=True) and stat.S_ISDIR(ROOT.lstat().st_mode), 'Release root has alias/symlink components')
    records = {}
    directories = set()
    for path in sorted(ROOT.rglob('*')):
        name = path.relative_to(ROOT).as_posix()
        require(safe_name(name), 'Unsafe release/archive path: ' + name)
        st = path.lstat()
        require(stat.S_ISREG(st.st_mode) or stat.S_ISDIR(st.st_mode), 'Special file or symlink in release')
        if stat.S_ISDIR(st.st_mode):
            directories.add(name)
        else:
            data = read(path)
            records[name] = {'sha256': sha(data), 'bytes': len(data), 'mode': stat.S_IMODE(st.st_mode), 'mtime_ns': st.st_mtime_ns}
    # Empty staging directories are permitted before publication, but recorded for preservation.
    return {'files': records, 'directories': sorted(directories)}

def content_inventory(snapshot):
    return {name: {'bytes': row['bytes'], 'sha256': row['sha256']} for name, row in snapshot['files'].items()}

def check_frozen(snapshot):
    raw = read(ROOT / 'INPUT_PINS.json')
    require(sha(raw) == INPUT_PINS_SHA256, 'Frozen input-pin map mismatch')
    pins = parse(raw)
    require(isinstance(pins, dict) and set(pins) == {'roots', 'files'} and pins['roots'] == ['science/frozen-proof', 'audits/scientific'], 'Invalid frozen pin schema')
    require(isinstance(pins['files'], dict) and all(safe_name(name) and row_valid(row) for name, row in pins['files'].items()), 'Invalid frozen file map')
    actual = {name: row for name, row in content_inventory(snapshot).items() if name.startswith('science/') or name.startswith('audits/scientific/')}
    require(actual == pins['files'], 'Frozen science/audit exact inventory mismatch')
    expected_dirs = {str(parent) for name in actual for parent in Path(name).parents if str(parent) == 'science' or str(parent).startswith('science/') or str(parent) == 'audits/scientific' or str(parent).startswith('audits/scientific/')}
    actual_dirs = {name for name in snapshot['directories'] if name == 'science' or name.startswith('science/') or name == 'audits/scientific' or name.startswith('audits/scientific/')}
    require(expected_dirs == actual_dirs, 'Frozen directory inventory mismatch')
    return pins

def check_manifest(pin=None):
    raw = read(ROOT / 'RELEASE_MANIFEST.json')
    require(pin is None or (isinstance(pin, str) and re.fullmatch(r'[0-9a-f]{64}', pin) and sha(raw) == pin), 'Manifest digest mismatch')
    manifest = parse(raw)
    require(isinstance(manifest, dict) and set(manifest) == {'report', 'format', 'scope', 'files'} and type(manifest['report']) is int and manifest['report'] == 61 and type(manifest['format']) is int and manifest['format'] == 1 and manifest['scope'] == 'Every regular release file except this manifest; ZIP separately hashed', 'Invalid release manifest schema')
    require(isinstance(manifest['files'], dict) and all(safe_name(name) and row_valid(row) for name, row in manifest['files'].items()), 'Invalid release manifest file map')
    current = content_inventory(full_inventory())
    current.pop('RELEASE_MANIFEST.json', None)
    require(current == manifest['files'], 'Release exact inventory/hash mismatch')
    return raw, manifest

def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B')
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='operation', required=True)
    sub.add_parser('prepare')
    command = sub.add_parser('seal')
    command.add_argument('--zip', required=True)
    command = sub.add_parser('verify')
    command.add_argument('--manifest-sha256', required=True)
    sub.add_parser('check-inputs')
    args = parser.parse_args()
    check_root()
    if args.operation == 'prepare':
        prepare()
    elif args.operation == 'seal':
        seal(args.zip)
    elif args.operation == 'verify':
        raw, manifest = check_manifest(args.manifest_sha256)
        print(encoded({'status': 'PASS', 'manifest_sha256': sha(raw), 'files': len(manifest['files'])}).decode(), end='')
    else:
        print('Frozen exact input inventory PASS')

if __name__ == '__main__':
    main()
