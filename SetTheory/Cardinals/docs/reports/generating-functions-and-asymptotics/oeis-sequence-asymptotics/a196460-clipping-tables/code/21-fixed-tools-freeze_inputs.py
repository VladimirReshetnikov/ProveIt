#!/usr/bin/env python3
"""Presentation-only source freezing and scoped metadata verification.
All upstream Python and other scientific programs are inert copied bytes.
Use python3 -I -S -B. This tool performs no subprocess calls or dynamic imports.
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

ROOT = Path(__file__).absolute().parent.parent
BASE = Path('/workspace/shared')
SOURCES = {
    'asymptotics': ('arity-table-asymptotics-20261004', '6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1'),
    'independent-audit': ('independent-arity-asymptotics-audit-20261004', '737af333985bc079ecdd688f1854f7221bb86169db7841d91a1115d2f94e7055'),
}
DEPENDENCIES = {
    'ONE_WITNESS.md': ('two-witness-tensor-compiler-20261004/ONE_WITNESS.md', '9135dd0e829adb3190e99ed1b62f8d419f9f7540cfd92a1acd1635726fa7172c'),
    'AUDIT.md': ('independent-low-arity-audit-20261004/AUDIT.md', '6bf14006170df1e126fb98d8e06ee97cfb51786f9ce11bcc0a37370a896d5afe'),
    'ONE_WITNESS_SOURCE_MANIFEST.sha256': ('two-witness-tensor-compiler-20261004/MANIFEST.sha256', None),
    'AUDIT_SOURCE_MANIFEST.sha256': ('independent-low-arity-audit-20261004/MANIFEST.sha256', None),
}
REPORTS = ('report69-low-arity-compilers-release-20261004', 'report70-two-scale-radius-release-20261004')


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
    require(path.is_absolute() and str(path) == str(path.absolute()), 'Absolute path required')
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
    r = {'kind': stat.S_IFMT(s.st_mode), 'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns, 'size': s.st_size}
    if stat.S_ISREG(s.st_mode):
        r['sha256'] = sha(read(path))
    return r


def inventory(path):
    return {str(p): row(p) for p in [path, *sorted(path.rglob('*'))]}


def verify_manifest(path, pin):
    data = read(path / 'MANIFEST.sha256')
    require(sha(data) == pin, 'Source manifest pin mismatch')
    records = {}
    for line in data.decode('utf-8').splitlines():
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match is not None, 'Malformed source manifest')
        digest, name = match.groups()
        require(name not in records and not name.startswith('/') and '\\' not in name and all(x not in ('', '.', '..') for x in name.split('/')), 'Unsafe source manifest name')
        records[name] = digest
    actual = {p.relative_to(path).as_posix() for p in path.rglob('*') if p.is_file()}
    require(actual == set(records) | {'MANIFEST.sha256'}, 'Source manifest file set mismatch')
    for name, digest in records.items():
        require(sha(read(path / name)) == digest, 'Source payload digest mismatch: ' + name)
    return {'manifest_sha256': pin, 'payload_files': len(records), 'exact_file_set': True}


def history():
    science = BASE / SOURCES['asymptotics'][0] / 'evidence'
    audit = BASE / SOURCES['independent-audit'][0] / 'original-history'
    names = ('input-before.json', 'input-current.json', 'input-changes.json', 'core-final.json', 'preservation-result.json', 'preservation.log')
    for name in names:
        require(read(science / name) == read(audit / name), 'Historical evidence copy mismatch')
    before = parse(read(science / 'input-before.json'))
    after = parse(read(science / 'input-current.json'))
    changes = parse(read(science / 'input-changes.json'))
    core = parse(read(science / 'core-final.json'))
    exact = {name: {'before': before.get(name), 'after': after.get(name)} for name in sorted(set(before) | set(after)) if before.get(name) != after.get(name)}
    require(exact == changes and len(changes) == 132, 'Historical changes mismatch')
    counts = {report: sum(name.startswith(str(BASE / report) + '/') or name == str(BASE / report) for name in changes) for report in REPORTS}
    require(counts == {REPORTS[0]: 44, REPORTS[1]: 88}, 'Historical report scope mismatch')
    require(len(core) == 62 and all(before.get(name) == after.get(name) == value for name, value in core.items()), 'Historic 62-entry core differs')
    require(all(row(Path(name)) == value for name, value in core.items()), 'Original 62-entry core changed')
    return core, {'historical_changes': 132, 'historical_report_change_counts': counts, 'core_entries': 62, 'core_bytes_modes_mtimes_unchanged': True, 'authentic_history_preserved': True, 'whole_historical_release_interval_preservation_claimed': False}


def original_snapshot(core):
    result = {name: row(Path(name)) for name in core}
    for name in [*[value[0] for value in SOURCES.values()], *REPORTS]:
        result.update(inventory(BASE / name))
    return result


def write_new(path, data):
    with path.open('xb') as f:
        f.write(data)


def pins_tree(path):
    files, dirs = {}, {}
    for p in sorted(path.rglob('*')):
        r = row(p); entry = {'mode': r['mode'], 'mtime_ns': r['mtime_ns']}
        if r['kind'] == stat.S_IFDIR:
            dirs[p.relative_to(ROOT).as_posix()] = entry
        else:
            files[p.relative_to(ROOT).as_posix()] = {**entry, 'bytes': r['size'], 'sha256': r['sha256']}
    s = path.stat()
    return {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}, files, dirs


def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('command', choices=('freeze', 'verify-originals'))
    ap.add_argument('--receipt-output')
    a = ap.parse_args(); canonical(ROOT)
    core, historical = history()
    before = original_snapshot(core)
    if a.command == 'verify-originals':
        frozen = parse(read(ROOT / 'qa/tool-original-inputs-before.json'))
        require(before == frozen, 'Scoped original input bytes/modes/mtimes changed')
        receipt = {'status': 'PASS', 'scoped_original_entries': len(before), 'fresh_interval_equal': True, **historical}
        if a.receipt_output:
            p = Path(a.receipt_output)
            require(p.is_absolute() and not p.exists(), 'Fresh absolute receipt output required')
            canonical(p.parent)
            require(p.parent == ROOT / 'qa' and p.name.startswith('tool-'), 'Receipt must be scoped QA tool output')
            write_new(p, encoded(receipt))
        print(encoded(receipt).decode()); return
    require(not (ROOT / 'inputs').exists(), 'Frozen inputs already exist')
    authentications = {name: verify_manifest(BASE / value[0], value[1]) for name, value in SOURCES.items()}
    for _, (relative, pin) in DEPENDENCIES.items():
        if pin:
            require(sha(read(BASE / relative)) == pin, 'Closure dependency pin mismatch')
    (ROOT / 'inputs').mkdir()
    for name, (relative, _) in SOURCES.items():
        shutil.copytree(BASE / relative, ROOT / 'inputs' / name, copy_function=shutil.copy2)
        target = ROOT / 'inputs' / name
        src_inv = {str(Path(key).relative_to(BASE / relative)): value for key, value in inventory(BASE / relative).items()}
        dst_inv = {str(Path(key).relative_to(target)): value for key, value in inventory(target).items()}
        # Directory allocation size is filesystem-specific; bytes, modes and mtimes are portable claims.
        for tree in (src_inv, dst_inv):
            for value in tree.values():
                if value['kind'] == stat.S_IFDIR: value.pop('size')
        require(src_inv == dst_inv, 'Copied source metadata mismatch')
    dep = ROOT / 'inputs/closure-dependencies'; dep.mkdir()
    dep_pins = {}
    for name, (relative, _) in DEPENDENCIES.items():
        source = BASE / relative; target = dep / name
        shutil.copy2(source, target)
        require(row(source) == row(target), 'Closure dependency metadata mismatch')
        dep_pins[name] = {'origin': str(source), **row(source)}
    roots, files, directories = {}, {}, {}
    roots['inputs'], files, directories = pins_tree(ROOT / 'inputs')
    pins = {'format': 'Arity asymptotics frozen input pins v1', 'roots': roots,
            'source_roots': {name: str(BASE / source[0]) for name, source in SOURCES.items()}, 'files': files, 'directories': directories}
    write_new(ROOT / 'INPUT_PINS.json', encoded(pins))
    write_new(ROOT / 'qa/tool-original-inputs-before.json', encoded(before))
    after = original_snapshot(core)
    require(before == after, 'Originals changed during source freeze')
    write_new(ROOT / 'qa/tool-original-inputs-after-freeze.json', encoded(after))
    write_new(ROOT / 'qa/tool-closure-dependency-pins.json', encoded(dep_pins))
    receipt = {'status': 'PASS', 'scope': 'Source/audit trees, 62-entry dependency core, and existing Report69/70 release trees; bytes/modes/nanosecond mtimes only; no scientific code execution',
               'source_manifests': authentications, 'frozen_files': len(files), 'input_pins_sha256': sha(encoded(pins)), 'scoped_original_entries': len(before), 'fresh_freeze_interval_equal': True, **historical}
    write_new(ROOT / 'qa/tool-input-freeze-receipt.json', encoded(receipt))
    print(encoded(receipt).decode())


if __name__ == '__main__':
    main()
