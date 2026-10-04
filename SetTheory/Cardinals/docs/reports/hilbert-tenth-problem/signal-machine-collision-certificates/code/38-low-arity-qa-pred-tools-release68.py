#!/usr/bin/env python3
"""Report68 release-only authentication, preparation, deterministic sealing and extraction.
Run with python3 -I -S -B. Never executes a scientific source program.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import zipfile

ROOT = Path(__file__).absolute().parent.parent
INPUT_PINS_SHA256 = '12705f524b493708684e95911b1eb96b1afbcc58668beb089d63730d85c28df5'
MANIFEST = 'RELEASE_MANIFEST.json'
FORMAT = 'Report68 release manifest v1'
MODULES = ('Report68.tex', 'arithmetic.tex', 'forward.tex', 'cutoffs.tex', 'inverse.tex', 'scope.tex')
PROTECTED = (Path('/workspace/shared/native-gap-counting-independent-review-20261004'), Path('/workspace/shared/native-gap-error-statistics-independent-audit-20261004'), Path('/workspace/shared/native-gap-error-statistics-independent-audit-20261004-v2'), Path('/workspace/shared/independent-inverse-statistics-audit-20261004'), Path('/workspace/shared/native-gap-counting-continuation-20261004'), Path('/workspace/shared/native-gap-error-statistics-20261004'), Path('/workspace/shared/native-gap-inverse-statistics-20261004'), Path('/workspace/shared/native-gap-halting-continuation-20261004'), Path('/workspace/shared/report66-bounded-certificates-counting-release-20261004'))


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)


def digest(value):
    require(isinstance(value, str) and re.fullmatch('[0-9a-f]{64}', value) is not None, 'Expected lowercase SHA-256 pin')
    return value


def relative_name(name):
    require(isinstance(name, str) and name and not name.startswith('/') and str(Path(name)) == name, 'Noncanonical relative path')
    require(all(x not in ('', '.', '..') for x in name.split('/')), 'Path traversal or alias')
    require(all(ord(c) >= 32 and c not in '\\' for c in name), 'Unsafe path character')
    return name


def canonical(path):
    raw = str(path)
    require(raw.startswith('/') and not raw.startswith('//') and str(Path(raw)) == raw, 'Canonical absolute path required')
    require(all(part not in ('.', '..') for part in raw.split('/')), 'Path alias')
    p = Path(raw)
    for parent in reversed([p, *p.parents]):
        s = parent.lstat()
        require(not stat.S_ISLNK(s.st_mode), 'Symlink path component: ' + str(parent))
        require(parent == p or stat.S_ISDIR(s.st_mode), 'Nondirectory ancestor')
    return p


def read(path):
    first = path.lstat()
    require(stat.S_ISREG(first.st_mode) and first.st_nlink == 1, 'Expected single-link regular file: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as stream:
        opened = os.fstat(stream.fileno())
        data = stream.read()
        after = os.fstat(stream.fileno())
    last = path.lstat()
    def identity(s):
        return (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(identity(first) == identity(opened) == identity(after) == identity(last), 'Input changed while reading: ' + str(path))
    return data


def inventory(root=ROOT, exclude_manifest=False, allow_empty=False):
    canonical(root)
    require(stat.S_ISDIR(root.lstat().st_mode), 'Root must be a directory')
    files, directories, identities = {}, {}, set()
    for path in sorted(root.rglob('*')):
        rel = relative_name(path.relative_to(root).as_posix())
        s = path.lstat()
        require(stat.S_ISDIR(s.st_mode) or stat.S_ISREG(s.st_mode), 'Nonregular tree entry: ' + rel)
        identity = (s.st_dev, s.st_ino)
        require(identity not in identities, 'Aliased filesystem object: ' + rel)
        identities.add(identity)
        row = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        if stat.S_ISDIR(s.st_mode):
            directories[rel] = row
        elif not (exclude_manifest and rel == MANIFEST):
            data = read(path)
            row.update(bytes=len(data), sha256=sha(data))
            files[rel] = row
    if not allow_empty:
        expected = {p.as_posix() for name in files for p in Path(name).parents if p.as_posix() != '.'}
        require(set(directories) == expected, 'Unexpected empty directory')
    return {'files': files, 'directories': directories}


def snapshot(root=ROOT, allow_empty=False):
    data = inventory(root, allow_empty=allow_empty)
    s = root.lstat()
    data['root'] = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
    return data


def new_output(raw, extra_protected=()):
    p = Path(raw)
    require(raw.startswith('/') and not raw.startswith('//') and str(p) == raw, 'Canonical absolute output required')
    require(all(x not in ('.', '..') for x in raw.split('/')), 'Output path alias')
    canonical(p.parent)
    require(not os.path.lexists(p), 'Output must be fresh')
    for protected in (ROOT, *PROTECTED, *extra_protected):
        require(p != protected and protected not in p.parents and p not in protected.parents, 'Output overlaps protected input: ' + str(protected))
        if protected.exists():
            # Canonical traversal rejects symlinks; samefile catches directory aliases.
            for parent in [p.parent, *p.parent.parents]:
                require(not os.path.samefile(parent, protected), 'Output ancestor aliases protected input')
    return p


def write_new(path, data):
    with path.open('xb') as stream:
        stream.write(data)


def check_inputs():
    raw = read(ROOT / 'INPUT_PINS.json')
    require(sha(raw) == INPUT_PINS_SHA256, 'Frozen input-pin map differs from inspected version')
    pins = parse(raw)
    require(set(pins) == {'format', 'roots', 'source_roots', 'files', 'directories'} and pins['format'] == 'Report68 frozen input pins v1', 'Invalid input-pin schema')
    scopes = {'science', 'audits'}
    files, directories = {}, {}
    for scope in sorted(scopes):
        tree = inventory(ROOT / scope)
        root_stat = (ROOT / scope).lstat()
        require({'mode': stat.S_IMODE(root_stat.st_mode), 'mtime_ns': root_stat.st_mtime_ns} == pins['roots'][scope], 'Frozen scope root metadata differs: ' + scope)
        files.update({scope + '/' + name: row for name, row in tree['files'].items()})
        directories.update({scope + '/' + name: row for name, row in tree['directories'].items()})
    require(files == pins['files'] and directories == pins['directories'], 'Frozen input inventory, bytes, mode or mtime differs')
    return pins


def flatten(require_pins=True, pin=None):
    folder = ROOT / 'manuscript'
    canonical(folder)
    require({p.name for p in folder.iterdir()} <= set(MODULES) | {'MANUSCRIPT_PINS.json'}, 'Unexpected manuscript entry')
    sources = {name: read(folder / name) for name in MODULES}
    pins = {name: sha(data) for name, data in sources.items()}
    if require_pins:
        raw = read(folder / 'MANUSCRIPT_PINS.json')
        require(sha(raw) == digest(pin), 'Manuscript pin map does not match external pin')
        require(parse(raw) == pins, 'Manuscript bytes differ from reviewed pin map')
    flat = sources['Report68.tex']
    for name in MODULES[1:]:
        token = ('\\input{manuscript/' + name + '}\n').encode()
        require(flat.count(token) == 1, 'Expected exactly one line input: ' + name)
        flat = flat.replace(token, sources[name])
    require(re.search(rb'\\(?:input|include)\s*\{', flat) is None, 'Unexpanded TeX input')
    if require_pins:
        require(read(ROOT / 'Report68.tex') == flat, 'Standalone LaTeX differs from deterministic flattening')
    return flat, pins


def validate_manifest(manifest):
    require(isinstance(manifest, dict) and set(manifest) == {'format', 'files', 'directories'} and manifest['format'] == FORMAT, 'Invalid manifest schema')
    require(isinstance(manifest['files'], dict) and isinstance(manifest['directories'], dict), 'Invalid manifest inventories')
    require(MANIFEST not in manifest['files'] and MANIFEST not in manifest['directories'], 'Self-referential manifest or manifest-directory collision')
    require(not (set(manifest['files']) & set(manifest['directories'])), 'File/directory overlap')
    for kind in ('files', 'directories'):
        for name, row in manifest[kind].items():
            relative_name(name)
            fields = {'mode', 'mtime_ns'} | ({'bytes', 'sha256'} if kind == 'files' else set())
            require(isinstance(row, dict) and set(row) == fields, 'Invalid manifest entry')
            require(type(row['mode']) is int and 0 <= row['mode'] <= 0o777, 'Unsafe mode')
            require(type(row['mtime_ns']) is int and row['mtime_ns'] >= 0, 'Invalid mtime')
            if kind == 'files':
                require(type(row['bytes']) is int and row['bytes'] >= 0, 'Invalid size')
                digest(row['sha256'])
    expected = {p.as_posix() for name in manifest['files'] for p in Path(name).parents if p.as_posix() != '.'}
    require(set(manifest['directories']) == expected, 'Missing or extraneous manifest directory')
    return manifest


def verify(pin):
    raw = read(ROOT / MANIFEST)
    require(sha(raw) == digest(pin), 'Manifest digest mismatch')
    manifest = validate_manifest(parse(raw))
    require(inventory(exclude_manifest=True) == {k: manifest[k] for k in ('files', 'directories')}, 'Release inventory, bytes, mode or mtime mismatch')
    check_inputs()
    return manifest, raw


def extract(archive_path, output, pin):
    canonical(archive_path)
    require(archive_path != output and archive_path not in output.parents, 'Archive/output overlap')
    archive_before = read(archive_path)
    with zipfile.ZipFile(archive_path) as archive:
        raw = archive.read('Report68/' + MANIFEST)
        require(sha(raw) == digest(pin), 'Archived manifest pin mismatch')
        manifest = validate_manifest(parse(raw))
        expected = ['Report68/' + name for name in sorted([*manifest['files'], MANIFEST])]
        require(archive.namelist() == expected, 'Archive inventory mismatch or duplicates')
        require(archive.testzip() is None, 'ZIP CRC failure')
        payload = {}
        for name in sorted([*manifest['files'], MANIFEST]):
            info = archive.getinfo('Report68/' + name)
            require(not info.is_dir() and info.create_system == 3 and stat.S_ISREG(info.external_attr >> 16), 'Nonregular ZIP entry')
            data = archive.read(info)
            if name != MANIFEST:
                row = manifest['files'][name]
                require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Archived bytes differ: ' + name)
                require(stat.S_IMODE(info.external_attr >> 16) == row['mode'], 'Archived mode differs')
            payload[name] = data
    output.mkdir(mode=0o700)
    for name in sorted(manifest['directories'], key=lambda n: (n.count('/'), n)):
        (output / name).mkdir()
    for name, data in payload.items():
        p = output / name
        write_new(p, data)
        row = manifest['files'].get(name, {'mode': 0o644, 'mtime_ns': 1791072000000000000})
        p.chmod(row['mode'])
        os.utime(p, ns=(row['mtime_ns'], row['mtime_ns']))
    for name, row in sorted(manifest['directories'].items(), key=lambda item: (-item[0].count('/'), item[0])):
        p = output / name
        p.chmod(row['mode'])
        os.utime(p, ns=(row['mtime_ns'], row['mtime_ns']))
    require(inventory(output, exclude_manifest=True) == {k: manifest[k] for k in ('files', 'directories')}, 'Extracted inventory differs')
    require(read(output / MANIFEST) == raw, 'Extracted manifest differs')
    require(read(archive_path) == archive_before, 'Archive changed during extraction')
    return {'status': 'PASS', 'files': len(payload), 'manifest_sha256': pin, 'output': str(output), 'bytes_modes_mtimes_restored': True}


def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B without optimization')
    canonical(Path(__file__).absolute())
    ap = argparse.ArgumentParser(description=__doc__)
    commands = ap.add_subparsers(dest='command', required=True)
    commands.add_parser('check-inputs')
    p = commands.add_parser('prepare'); p.add_argument('--output-dir', required=True)
    p = commands.add_parser('manifest'); p.add_argument('--output', required=True)
    p = commands.add_parser('verify'); p.add_argument('--manifest-sha256', required=True)
    p = commands.add_parser('archive'); p.add_argument('--manifest-sha256', required=True); p.add_argument('--output', required=True)
    p = commands.add_parser('extract'); p.add_argument('--manifest-sha256', required=True); p.add_argument('--archive', required=True); p.add_argument('--output-dir', required=True)
    a = ap.parse_args()
    if a.command == 'extract':
        before = snapshot(allow_empty=True)
        receipt = extract(Path(a.archive), new_output(a.output_dir, (Path(a.archive),)), a.manifest_sha256)
        require(snapshot(allow_empty=True) == before, 'Release changed during extraction')
        print(encoded(receipt).decode()); return
    before = snapshot(allow_empty=a.command in ('check-inputs', 'prepare'))
    try:
        pins = check_inputs()
        if a.command == 'check-inputs':
            receipt = {'status': 'PASS', 'frozen_files': len(pins['files']), 'input_pins_sha256': INPUT_PINS_SHA256}
        elif a.command == 'prepare':
            out = new_output(a.output_dir); flat, manuscript_pins = flatten(False)
            out.mkdir(mode=0o700)
            write_new(out / 'Report68.tex', flat); write_new(out / 'MANUSCRIPT_PINS.json', encoded(manuscript_pins))
            receipt = {'status': 'PASS', 'output': str(out), 'standalone_sha256': sha(flat), 'manuscript_pins_sha256': sha(encoded(manuscript_pins))}
        elif a.command == 'manifest':
            out = new_output(a.output)
            manifest = {'format': FORMAT, **inventory(exclude_manifest=True)}
            validate_manifest(manifest); data = encoded(manifest); write_new(out, data)
            receipt = {'status': 'PASS', 'manifest_sha256': sha(data), 'files': len(manifest['files']), 'output': str(out)}
        else:
            manifest, raw = verify(a.manifest_sha256)
            receipt = {'status': 'PASS', 'manifest_sha256': a.manifest_sha256, 'files': len(manifest['files'])}
            if a.command == 'archive':
                out = new_output(a.output)
                payload = {name: read(ROOT / name) for name in manifest['files']}; payload[MANIFEST] = raw
                with out.open('xb') as stream:
                    with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
                        for name, data in sorted(payload.items()):
                            entry = zipfile.ZipInfo('Report68/' + name, date_time=(2026, 10, 4, 0, 0, 0))
                            entry.create_system = 3
                            entry.external_attr = (stat.S_IFREG | manifest['files'].get(name, {'mode': 0o644})['mode']) << 16
                            archive.writestr(entry, data, compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
                with zipfile.ZipFile(out) as archive:
                    require(archive.testzip() is None and archive.namelist() == ['Report68/' + name for name in sorted(payload)], 'ZIP inventory/CRC failure')
                    require(all(archive.read('Report68/' + name) == data for name, data in payload.items()), 'ZIP content mismatch')
                receipt.update(zip_sha256=sha(read(out)), output=str(out), bytes=out.stat().st_size)
    finally:
        require(snapshot(allow_empty=a.command in ('check-inputs', 'prepare')) == before, 'Release changed during operation')
    print(encoded(receipt).decode())


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, zipfile.BadZipFile) as error:
        print('RELEASE REFUSED: ' + str(error), file=sys.stderr)
        raise SystemExit(2)
