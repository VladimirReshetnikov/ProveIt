#!/usr/bin/env python3
"""Independent release-tool adversarial checks. No scientific source execution."""
import copy
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import stat
import struct
import subprocess
import sys
import zipfile
import zlib

BASE = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).absolute().parent
ROOT = BASE / 'reviewed-release'
RESULTS = []
H = runpy.run_path(str(ROOT / 'tools/release62.py'), run_name='review_release_helpers')
B = runpy.run_path(str(ROOT / 'tools/build_report62.py'), run_name='review_png_helper')

def require(value, message):
    if not value:
        raise ValueError(message)

def pin(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def snapshot(root):
    rows = {}
    for path in [root, *sorted(root.rglob('*'))]:
        s = path.lstat()
        row = {'dev': s.st_dev, 'ino': s.st_ino, 'mode': s.st_mode,
               'nlink': s.st_nlink, 'size': s.st_size, 'mtime_ns': s.st_mtime_ns}
        if stat.S_ISREG(s.st_mode):
            row['sha256'] = pin(path)
        rows[str(path.relative_to(root))] = row
    return rows

def clone(label, source=ROOT):
    dest = BASE / ('supplemental-fixture-' + label)
    shutil.copytree(source, dest, copy_function=shutil.copy2)
    return dest

def command(label, args, root=ROOT, expected_success=False, output=None, env=None):
    before = snapshot(root)
    commandline = [sys.executable, '-I', '-S', '-B', str(root / 'tools' / args[0]), *args[1:]]
    result = subprocess.run(commandline, cwd=BASE, env=env, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=360)
    after = snapshot(root)
    require((result.returncode == 0) == expected_success, label + ': unexpected exit ' + str(result.returncode) + result.stdout.decode(errors='replace')[-1000:])
    require(before == after, label + ': input mutation')
    if output is not None and not expected_success:
        require(not os.path.lexists(output), label + ': output created before rejection')
    RESULTS.append({'name': label, 'status': 'PASS', 'returncode': result.returncode,
                    'source_preserved': True, 'stdout': result.stdout.decode(errors='replace')})
    return result

def rejection(label, func):
    try:
        func()
    except (ValueError, TypeError, KeyError, OSError, zlib.error):
        RESULTS.append({'name': label, 'status': 'PASS'})
    else:
        raise ValueError(label + ': invalid value was accepted')

def record(label, value):
    require(value, label)
    RESULTS.append({'name': label, 'status': 'PASS'})

def chunk(kind, data):
    return struct.pack('>I', len(data)) + kind + data + struct.pack('>I', zlib.crc32(kind + data) & 0xffffffff)

def png(parts):
    return b'\x89PNG\r\n\x1a\n' + b''.join(chunk(k, d) for k, d in parts)

def main():
    initial_sources = {name: pin(ROOT / 'tools' / name) for name in ('release62.py', 'build_report62.py', 'selftest62.py', 'BUILD_DEPENDENCIES_LOCK.json')}
    original_roots = [Path('/workspace/shared/projective-signal-shears62-20261004'), Path('/workspace/shared/audit-projective-signal-shears62-20261004'), Path('/workspace/shared/five-signal-planar-realization60-20261004'), Path('/workspace/shared/fixed-word-invertibility61-20261004')]
    original_before = {str(p): snapshot(p) for p in original_roots}
    (BASE / 'ORIGINAL_INPUTS_BEFORE.json').write_text(json.dumps(original_before, sort_keys=True, indent=2) + '\n')
    command('complete-original-input-authentication', ['release62.py', 'check-inputs'], expected_success=True)
    pins = json.loads((ROOT / 'INPUT_PINS.json').read_text())
    for i, name in enumerate(pins['files']):
        root = clone('tamper-' + str(i))
        path = root / name
        s = path.stat()
        data = path.read_bytes()
        require(bool(data), 'expected nonempty fixture file')
        path.write_bytes(bytes([data[0] ^ 1]) + data[1:])
        os.utime(path, ns=(s.st_atime_ns, s.st_mtime_ns))
        command('same-length-same-mtime-tamper-' + name, ['release62.py', 'check-inputs'], root=root)
    for i, name in enumerate(pins['directories']):
        root = clone('directory-mode-' + str(i))
        path = root / name
        path.chmod(stat.S_IMODE(path.stat().st_mode) ^ 0o020)
        command('frozen-directory-mode-' + name, ['release62.py', 'check-inputs'], root=root)
    root = clone('missing-frozen')
    (root / 'science/frozen-proof/PROOF.md').unlink()
    command('missing-frozen-file', ['release62.py', 'check-inputs'], root=root)
    root = clone('frozen-fifo')
    os.mkfifo(root / 'audits/scientific/unexpected.fifo')
    command('reject-frozen-fifo', ['release62.py', 'check-inputs'], root=root)
    root = clone('input-map-tamper')
    p = root / 'INPUT_PINS.json'; p.write_bytes(p.read_bytes() + b' ')
    command('input-map-authenticated-before-parse', ['release62.py', 'check-inputs'], root=root)
    for label, output in [('doubled-slash', str(BASE) + '//alias-new'), ('dot-component', str(BASE) + '/./alias-new'), ('trailing-slash', str(BASE) + '/alias-new/'), ('double-root-slash', '/' + str(BASE) + '/alias-new'), ('empty-output', ''), ('ancestor-output', '/workspace'), ('frozen-output', str(ROOT / 'science/frozen-proof/new'))]:
        command('path-' + label, ['release62.py', 'prepare', '--output-dir', output])
    dangling = BASE / 'dangling-output'; dangling.symlink_to(BASE / 'absent-target')
    command('reject-dangling-output', ['release62.py', 'prepare', '--output-dir', str(dangling)])
    root = clone('external-hardlink')
    os.link(root / 'README.md', BASE / 'external-hardlink-to-input')
    command('reject-hardlink-outside-release', ['release62.py', 'check-inputs'], root=root)

    for raw in [b'{"x":1,"x":2}', b'{"outer":{"x":1,"x":2}}']:
        rejection('duplicate-json-key-' + pin_bytes(raw), lambda raw=raw: H['parse'](raw))
    valid = {'format': H['FORMAT'], 'files': {'dir/file': {'mode': 0o644, 'mtime_ns': 10, 'bytes': 3, 'sha256': hashlib.sha256(b'abc').hexdigest()}}, 'directories': {'dir': {'mode': 0o755, 'mtime_ns': 10}}}
    record('valid-manifest-schema', H['validate_manifest'](valid) == valid)
    mutations = []
    for field, value in [('mode', True), ('mode', 0o4755), ('mode', -1), ('mtime_ns', True), ('mtime_ns', -1), ('bytes', True), ('bytes', -1), ('sha256', 'A' * 64), ('sha256', '0' * 63)]:
        obj = copy.deepcopy(valid); obj['files']['dir/file'][field] = value; mutations.append((field + '-' + str(value), obj))
    for name in ['../escape', '/absolute', 'dir//file', 'dir/./file', 'dir/../file', 'dir\\file', 'bad\nname', 'dir/file/']:
        obj = copy.deepcopy(valid); obj['files'][name] = obj['files'].pop('dir/file'); mutations.append(('name-' + repr(name), obj))
    obj = copy.deepcopy(valid); obj['files'][H['MANIFEST']] = obj['files'].pop('dir/file'); mutations.append(('manifest-self', obj))
    obj = copy.deepcopy(valid); obj['files'][H['MANIFEST'] + '/child'] = obj['files'].pop('dir/file'); obj['directories'] = {H['MANIFEST']: {'mode': 0o755, 'mtime_ns': 10}}; mutations.append(('manifest-reserved-directory', obj))
    obj = copy.deepcopy(valid); obj['directories'] = {}; mutations.append(('missing-directory', obj))
    obj = copy.deepcopy(valid); obj['directories']['empty'] = {'mode': 0o755, 'mtime_ns': 10}; mutations.append(('extra-directory', obj))
    obj = copy.deepcopy(valid); obj['files']['dir'] = obj['files']['dir/file']; mutations.append(('file-directory-overlap', obj))
    for label, obj in mutations:
        rejection('manifest-schema-' + label, lambda obj=obj: H['validate_manifest'](obj))

    ihdr = (b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 2, 0, 0, 0))
    idat = (b'IDAT', zlib.compress(b'\x00\x00\x00\x00'))
    end = (b'IEND', b'')
    record('valid-png-raster', B['validate_png'](png([ihdr, idat, end]), require) == {'width': 1, 'height': 1})
    png_cases = {'duplicate-ihdr': [ihdr, ihdr, idat, end], 'missing-data': [ihdr, end], 'missing-end': [ihdr, idat], 'invalid-filter': [ihdr, (b'IDAT', zlib.compress(b'\x05\x00\x00\x00')), end], 'extra-raster-byte': [ihdr, (b'IDAT', zlib.compress(b'\x00' * 5)), end], 'short-raster': [ihdr, (b'IDAT', zlib.compress(b'\x00' * 3)), end], 'two-zlib-streams': [ihdr, (b'IDAT', idat[1] + idat[1]), end], 'unknown-chunk': [ihdr, (b'tEXt', b'abc'), idat, end], 'late-phys': [ihdr, idat, (b'pHYs', struct.pack('>IIB', 1, 1, 1)), end], 'zero-density': [ihdr, (b'pHYs', struct.pack('>IIB', 0, 1, 1)), idat, end], 'nonempty-iend': [ihdr, idat, (b'IEND', b'x')], 'zero-width': [(b'IHDR', struct.pack('>IIBBBBB', 0, 1, 8, 2, 0, 0, 0)), idat, end], 'bad-format': [(b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 6, 0, 0, 0)), idat, end]}
    for label, parts in png_cases.items():
        rejection('png-' + label, lambda parts=parts: B['validate_png'](png(parts), require))
    record('valid-split-idat', B['validate_png'](png([ihdr, (b'IDAT', idat[1][:3]), (b'IDAT', idat[1][3:]), end]), require) == {'width': 1, 'height': 1})
    mutable = BASE / 'stable-read-probe'; mutable.write_bytes(b'abc')
    original_open = os.open
    def mutate_during_open(path, flags, *args, **kwargs):
        fd = original_open(path, flags, *args, **kwargs)
        mutable.write_bytes(b'xyz')
        return fd
    try:
        os.open = mutate_during_open
        rejection('stable-read-detects-intervening-mutation', lambda: H['read'](mutable))
    finally:
        os.open = original_open

    owned = BASE / 'author-selftest-replay'
    archive = owned / 'archive-a.zip'
    manifest_pin = pin(owned / 'manifest.json')
    for label in ['duplicate', 'absolute', 'traversal', 'symlink-mode', 'wrong-mode', 'corrupt-payload']:
        bad = BASE / ('archive-' + label + '.zip')
        with zipfile.ZipFile(archive) as src, zipfile.ZipFile(bad, 'w') as dst:
            infos = src.infolist()
            target = next(info.filename for info in infos if info.filename.endswith('/README.md'))
            for old in infos:
                info = copy.copy(old); data = src.read(old)
                if info.filename == target:
                    if label == 'absolute': info.filename = '/escape'
                    if label == 'traversal': info.filename = 'Report62/../escape'
                    if label == 'symlink-mode': info.external_attr = (stat.S_IFLNK | 0o644) << 16
                    if label == 'wrong-mode': info.external_attr = (stat.S_IFREG | 0o600) << 16
                    if label == 'corrupt-payload': data = bytes([data[0] ^ 1]) + data[1:]
                dst.writestr(info, data)
            if label == 'duplicate':
                dst.writestr(infos[0], src.read(infos[0]))
        output = BASE / ('extract-rejected-' + label)
        command('archive-' + label, ['release62.py', 'extract', '--archive', str(bad), '--manifest-sha256', manifest_pin, '--output-dir', str(output)], output=output)
    output = BASE / 'extract-wrong-pin'
    command('archive-wrong-external-pin', ['release62.py', 'extract', '--archive', str(archive), '--manifest-sha256', '0' * 64, '--output-dir', str(output)], output=output)
    output = BASE / 'independent-roundtrip'
    command('independent-archive-roundtrip', ['release62.py', 'extract', '--archive', str(archive), '--manifest-sha256', manifest_pin, '--output-dir', str(output)], output=output, expected_success=True)
    command('independent-relocated-manifest', ['release62.py', 'verify', '--manifest-sha256', manifest_pin], root=output, expected_success=True)
    original_after = {str(p): snapshot(p) for p in original_roots}
    (BASE / 'ORIGINAL_INPUTS_AFTER.json').write_text(json.dumps(original_after, sort_keys=True, indent=2) + '\n')
    record('all-original-inputs-preserved', original_before == original_after)
    final_sources = {name: pin(ROOT / 'tools' / name) for name in initial_sources}
    record('reviewed-tool-sources-preserved', initial_sources == final_sources)
    result = {'status': 'PASS', 'scope': 'Independent release-only supplemental checks; no scientific executable run', 'tool_sources': initial_sources, 'test_count': len(RESULTS), 'tests': RESULTS}
    (BASE / 'SUPPLEMENTAL_RESULTS.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'test_count': len(RESULTS)}))

def pin_bytes(data):
    return hashlib.sha256(data).hexdigest()[:12]

if __name__ == '__main__':
    main()
