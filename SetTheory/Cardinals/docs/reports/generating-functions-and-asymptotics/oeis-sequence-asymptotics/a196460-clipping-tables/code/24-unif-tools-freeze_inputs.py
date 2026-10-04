#!/usr/bin/env python3
"""Freeze inert evidence and verify a scoped original content/metadata boundary.
Use python3 -I -S -B. No subprocesses, dynamic imports or scientific execution.
Access times, ownership, inode allocation, ctime and directory sizes are excluded.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import sys
import zipfile

ROOT = Path(__file__).absolute().parent.parent
BASE = Path('/workspace/shared')
SOURCES = {
    'uniform-sectors': ('growing-sector-truncations-20261004', 'bf48296dc1bd86689df3dbef9cb3bba99903ec84a32f226e2289ec79ea0a3a29', '5155553958eb14f2a2bb0c28aa1262cc2e2ad1871aac3b37d6d3efc2c7355c42'),
    'independent-audit': ('independent-growing-sector-audit-20261004', '039c112bd070a8b48b92584c76ec05b3876662bb82f186813a0fb445ddd9e36c', 'a9f4bd10377462b1430da6579d02f0d920985c17344c4f4c6e43fab7d38b40f3'),
}
PREDECESSOR = 'oeis-arity-asymptotics-release-20261004'
PREDECESSOR_MANIFEST_SHA = '313fe6210e10e3053ff518a591dc46c86c29681618775be67f0f87474ca4584c'
PREDECESSOR_ARCHIVE = 'A196460-clipping-tables-source-evidence-20261004.zip'
PREDECESSOR_ARCHIVE_SHA = '821a1cfc1c00fd6d109ee2f6ff8007b4e8985f03d45f6f9a04d07aa8623fde27'
PRIMARY_PINS = {
    'growing-sector-truncations-20261004/PROOF.md': 'ebd92e3b5bdf684981b2ff248376ac290c57aec403169beee780fef9ea92aa65',
    'independent-growing-sector-audit-20261004/AUDIT.md': '4fa84b2ddfe383668c86ea0ad4d7419b0304eb0d9a97725aecbdab7e3b63ff03',
}


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key')
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique)


def canonical(path):
    raw = str(path)
    require(path.is_absolute() and not raw.startswith('//') and not any(x in ('.', '..') for x in raw.split('/')), 'Canonical absolute path required')
    for p in [path, *path.parents]:
        require(not stat.S_ISLNK(p.lstat().st_mode), 'Symlink input')
    return path


def read(path):
    canonical(path)
    first = path.lstat()
    require(stat.S_ISREG(first.st_mode) and first.st_nlink == 1, 'Single-link regular file required')
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as f:
        opened = os.fstat(f.fileno()); data = f.read(); after = os.fstat(f.fileno())
    last = path.lstat()
    identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(identity(first) == identity(opened) == identity(after) == identity(last), 'Input changed during read')
    return data


def row(path):
    canonical(path); s = path.lstat()
    require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Unsafe input kind')
    r = {'kind': 'file' if stat.S_ISREG(s.st_mode) else 'directory', 'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
    if stat.S_ISREG(s.st_mode):
        data = read(path); r.update(size=len(data), sha256=sha(data))
    return r


def inventory(path):
    return {str(p): row(p) for p in [path, *sorted(path.rglob('*'))]}


def relative(name):
    require(isinstance(name, str) and name and not name.startswith('/') and '\\' not in name and all(x not in ('', '.', '..') for x in name.split('/')) and all(ord(x) >= 32 for x in name), 'Unsafe manifest name')
    return name


def verify_archive(path, pin, prefix, files, manifest_self_excluded=False):
    require(sha(read(path)) == pin, 'Source archive digest mismatch')
    with zipfile.ZipFile(path) as archive:
        expected = [prefix + '/' + name for name in sorted(files)]
        require(archive.namelist() == expected, 'Source archive inventory/ordering mismatch')
        require(archive.testzip() is None, 'Source archive CRC failure')
        for name, source in files.items():
            info = archive.getinfo(prefix + '/' + name)
            require(info.create_system == 3 and stat.S_ISREG(info.external_attr >> 16), 'Nonregular source ZIP entry')
            expected_mode = 0o644 if manifest_self_excluded and name == 'RELEASE_MANIFEST.json' else stat.S_IMODE(source.stat().st_mode)
            require(stat.S_IMODE(info.external_attr >> 16) == expected_mode, 'Source archive mode mismatch: ' + name)
            require(archive.read(info) == read(source), 'Source archive payload mismatch')
    return {'archive_sha256': pin, 'archive_members': len(files), 'exact_inventory_bytes_modes': True, 'manifest_self_mode_normalized': manifest_self_excluded}


def verify_manifest(path, pin, archive_pin):
    data = read(path / 'MANIFEST.sha256')
    require(sha(data) == pin, 'Source manifest pin mismatch')
    records = {}
    for line in data.decode('utf-8').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'Malformed source manifest')
        digest, name = match.groups(); relative(name)
        require(name not in records, 'Duplicate source name'); records[name] = digest
    actual = {p.relative_to(path).as_posix() for p in path.rglob('*') if p.is_file()}
    require(actual == set(records) | {'MANIFEST.sha256'}, 'Source manifest file set mismatch')
    for name, digest in records.items():
        require(sha(read(path / name)) == digest, 'Source payload digest mismatch: ' + name)
    archives = verify_archive(Path(str(path) + '.zip'), archive_pin, path.name, {name: path / name for name in actual})
    return {'manifest_sha256': pin, 'payload_files': len(records), 'exact_file_set': True, **archives}


def verify_predecessor():
    source = BASE / PREDECESSOR
    raw = read(source / 'RELEASE_MANIFEST.json')
    require(sha(raw) == PREDECESSOR_MANIFEST_SHA, 'Predecessor manifest digest mismatch')
    manifest = parse(raw)
    require(set(manifest) == {'format', 'files', 'directories'} and manifest['format'] == 'ArityAsymptotics release manifest v1', 'Predecessor manifest schema')
    actual = inventory(source)
    files, dirs = {}, {}
    for full, value in actual.items():
        name = Path(full).relative_to(source).as_posix()
        if name in ('.', 'RELEASE_MANIFEST.json'): continue
        relative(name)
        entry = {'mode': value['mode'], 'mtime_ns': value['mtime_ns']}
        if value['kind'] == 'file': files[name] = {**entry, 'bytes': value['size'], 'sha256': value['sha256']}
        else: dirs[name] = entry
    require(files == manifest['files'] and dirs == manifest['directories'], 'Predecessor bytes/modes/mtime inventory differs')
    archives = verify_archive(BASE / PREDECESSOR_ARCHIVE, PREDECESSOR_ARCHIVE_SHA, 'ArityAsymptotics', {name: source / name for name in [*files, 'RELEASE_MANIFEST.json']}, manifest_self_excluded=True)
    return {'manifest_sha256': PREDECESSOR_MANIFEST_SHA, 'files': len(files) + 1, 'bytes_modes_mtimes_equal': True, **archives}


def history_boundary():
    audit = BASE / SOURCES['independent-audit'][0] / 'evidence'
    before = parse(read(audit / 'input-before.json'))
    after = parse(read(audit / 'input-after.json'))
    require(before['objects'] == after['objects'] and len(before['objects']) == 333, 'Audit historical boundary mismatch')
    result = {}
    for value in before['objects']:
        path = value['path']; expected = dict(value); del expected['path']
        if expected['kind'] == 'directory': expected.pop('size', None)
        require(path not in result and path.startswith(str(BASE) + '/'), 'Duplicate/outside historical object')
        require(row(Path(path)) == expected, 'Historical input differs now: ' + path)
        result[path] = expected
    for path, value in result.items():
        if value['kind'] == 'directory':
            require(all(str(p) in result for p in Path(path).rglob('*')), 'Unrecorded object under historical directory: ' + path)
    source = BASE / SOURCES['uniform-sectors'][0] / 'evidence'
    sb = parse(read(source / 'input-before.json'))
    sa = parse(read(source / 'input-after.json'))
    require(sb['objects'] == sa['objects'] and len(sb['objects']) == 51, 'Source historical boundary mismatch')
    for value in sb['objects']:
        expected = dict(value); path = expected.pop('path')
        if expected['kind'] == 'directory': expected.pop('size', None)
        require(result.get(path) == expected, 'Source history outside verified audit boundary')
    return result


def original_snapshot():
    result = history_boundary()
    for name in [*[value[0] for value in SOURCES.values()], PREDECESSOR]:
        result.update(inventory(BASE / name))
    for name in [*[value[0] + suffix for value in SOURCES.values() for suffix in ('.zip', '-receipt.json')], PREDECESSOR_ARCHIVE]:
        result[str(BASE / name)] = row(BASE / name)
    return result


def write_new(path, data):
    with path.open('xb') as f: f.write(data)


def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('command', choices=('freeze', 'verify-originals'))
    ap.add_argument('--receipt-output')
    a = ap.parse_args(); canonical(ROOT)
    before = original_snapshot()
    if a.command == 'verify-originals':
        frozen = parse(read(ROOT / 'qa/tool-original-inputs-before.json'))
        require(before == frozen, 'Scoped original input bytes/modes/mtimes changed')
        receipt = {'status': 'PASS', 'scoped_original_entries': len(before), 'fresh_interval_equal': True, 'historical_333_object_audit_boundary_unchanged': True, 'historical_51_object_source_boundary_equal': True, 'atime_excluded': True, 'no_scientific_execution': True}
        if a.receipt_output:
            p = Path(a.receipt_output); canonical(p.parent)
            require(p.is_absolute() and not p.exists() and p.parent == ROOT / 'qa' and p.name.startswith('tool-'), 'Fresh scoped QA tool receipt required')
            write_new(p, encoded(receipt))
        print(encoded(receipt).decode()); return
    require(not (ROOT / 'inputs').exists(), 'Frozen inputs already exist')
    for relative_path, pin in PRIMARY_PINS.items():
        require(sha(read(BASE / relative_path)) == pin, 'Primary proof/audit pin mismatch')
    authentic = {name: verify_manifest(BASE / value[0], value[1], value[2]) for name, value in SOURCES.items()}
    predecessor = verify_predecessor()
    inputs = ROOT / 'inputs'; inputs.mkdir()
    for name, source in [(name, BASE / value[0]) for name, value in SOURCES.items()] + [('predecessor-release', BASE / PREDECESSOR)]:
        target = inputs / name
        shutil.copytree(source, target, copy_function=shutil.copy2)
        sr = {str(Path(k).relative_to(source)): v for k, v in inventory(source).items()}
        tr = {str(Path(k).relative_to(target)): v for k, v in inventory(target).items()}
        require(sr == tr, 'Copied evidence content/metadata mismatch')
    companions = inputs / 'source-seals'; companions.mkdir()
    for name in [*[value[0] + suffix for value in SOURCES.values() for suffix in ('.zip', '-receipt.json')], PREDECESSOR_ARCHIVE]:
        shutil.copy2(BASE / name, companions / name)
        require(row(BASE / name) == row(companions / name), 'Copied companion metadata mismatch')
    roots, files, dirs = {}, {}, {}
    for full, value in inventory(inputs).items():
        name = Path(full).relative_to(ROOT).as_posix()
        entry = {'mode': value['mode'], 'mtime_ns': value['mtime_ns']}
        if name == 'inputs': roots[name] = entry
        elif value['kind'] == 'directory': dirs[name] = entry
        else: files[name] = {**entry, 'bytes': value['size'], 'sha256': value['sha256']}
    pins = {'format': 'Uniform sectors frozen input pins v1', 'roots': roots, 'source_roots': {name: str(BASE / value[0]) for name, value in SOURCES.items()} | {'predecessor-release': str(BASE / PREDECESSOR)}, 'files': files, 'directories': dirs}
    write_new(ROOT / 'INPUT_PINS.json', encoded(pins))
    write_new(ROOT / 'qa/tool-original-inputs-before.json', encoded(before))
    after = original_snapshot(); require(before == after, 'Originals changed during source freeze')
    write_new(ROOT / 'qa/tool-original-inputs-after-freeze.json', encoded(after))
    receipt = {'status': 'PASS', 'scope': 'New proof/audit trees and seals, complete predecessor release and archive, and historical 333-object audit boundary; content, file sizes, modes, nanosecond mtimes and object set; excludes atime, ctime, owner and directory sizes', 'source_manifests': authentic, 'predecessor_authentication': predecessor, 'frozen_files': len(files), 'frozen_directories': len(dirs), 'input_pins_sha256': sha(encoded(pins)), 'scoped_original_entries': len(before), 'fresh_freeze_interval_equal': True, 'historical_333_object_audit_boundary_unchanged': True, 'historical_51_object_source_boundary_equal': True, 'no_scientific_execution': True, 'whole_historical_workspace_preservation_claimed': False}
    write_new(ROOT / 'qa/tool-input-freeze-receipt.json', encoded(receipt))
    print(encoded(receipt).decode())


if __name__ == '__main__':
    main()
