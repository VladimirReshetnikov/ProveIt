#!/usr/bin/env python3
"""Fresh independent synthetic/adversarial presentation tests; no science imports."""
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
import warnings
import zipfile
import zlib

C = Path('/workspace/shared/report69-tool-review-candidate-v5')
BASE = Path('/workspace/shared/report69-independent-release-tool-review-20261004')
O = BASE / 'adversarial-v2'
O.mkdir(mode=0o700)
H = runpy.run_path(str(C / 'tools/release69.py'), run_name='independent_release_inspection')
B = runpy.run_path(str(C / 'tools/build_report69.py'), run_name='independent_builder_inspection')
RESULTS = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def enc(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()

def passed(label, **details):
    RESULTS.append({'test': label, 'status': 'PASS', **details})

def rejects(label, fn):
    try:
        fn()
    except (ValueError, OSError, KeyError, zipfile.BadZipFile, zlib.error, json.JSONDecodeError) as error:
        passed(label, rejection=str(error))
    else:
        raise AssertionError('Accepted invalid input: ' + label)

def cli(label, args, root=C, success=False, isolated=True):
    cmd = [sys.executable, *(['-I', '-S', '-B'] if isolated else ['-B']), str(root / 'tools/release69.py'), *args]
    result = subprocess.run(cmd, cwd=O, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90)
    (O / (label + '.stdout')).write_bytes(result.stdout)
    assert (result.returncode == 0) == success, (label, result.stdout[-4000:])
    passed(label, exit_status=result.returncode)

def chunk(kind, data):
    return struct.pack('>I', len(data)) + kind + data + struct.pack('>I', zlib.crc32(kind + data) & 0xffffffff)

def png(width=1, height=1, depth=8, color=2, interlace=0, pixels=b'\x00\x11\x22\x33', before=b'', after=b'', stream=None):
    header = struct.pack('>IIBBBBB', width, height, depth, color, 0, 0, interlace)
    return b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', header) + before + chunk(b'IDAT', zlib.compress(pixels) if stream is None else stream) + after + chunk(b'IEND', b'')

def archive(label, manifest, content=b'Hello, Report69.\n', raw=None, transform=None):
    raw = enc(manifest) if raw is None else raw
    members = [('Report69/RELEASE_MANIFEST.json', raw, stat.S_IFREG | 0o644, 3),
               ('Report69/a/data.txt', content, stat.S_IFREG | 0o640, 3)]
    if transform:
        members = transform(members)
    target = O / (label + '.zip')
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', UserWarning)
        with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_DEFLATED) as z:
            for name, data, mode, system in members:
                item = zipfile.ZipInfo(name)
                item.create_system = system
                item.external_attr = mode << 16
                z.writestr(item, data)
    return target, sha(raw)

def reject_archive(label, manifest, **kwargs):
    path, pin = archive(label, manifest, **kwargs)
    output = O / (label + '-output')
    cli(label, ['extract', '--archive', str(path), '--output-dir', str(output), '--manifest-sha256', pin])
    assert not output.exists(), 'Invalid archive created output: ' + label

def main():
    # Direct parser and schema probes cannot be made to pass by merely re-pinning bad JSON.
    row = {'mode': 0o640, 'mtime_ns': 1791072000123456789, 'bytes': 17, 'sha256': sha(b'Hello, Report69.\n')}
    row['bytes'] = len(b'Hello, Report69.\n')
    manifest = {'format': H['FORMAT'], 'files': {'a/data.txt': row}, 'directories': {'a': {'mode': 0o750, 'mtime_ns': 1791072000987654321}}}
    assert H['validate_manifest'](manifest) == manifest
    passed('valid-manifest-schema')
    for value in ('../x', '/x', 'a/../x', './x', 'a//x', 'a/./x', 'a\\x', 'x\nq', 'x\x00q', ''):
        rejects('reject-relative-path-' + repr(value), lambda value=value: H['relative_name'](value))
    for value in ('A' * 64, '0' * 63, '0' * 65, 0, None, '0' * 64 + '\n'):
        rejects('reject-digest-' + repr(value), lambda value=value: H['digest'](value))
    rejects('duplicate-json-key', lambda: H['parse'](b'{"x":1,"x":2}'))
    rejects('nested-duplicate-json-key', lambda: H['parse'](b'{"x":{"mode":1,"mode":2}}'))
    mutations = []
    def mutate(label, fn):
        m = copy.deepcopy(manifest); fn(m); mutations.append((label, m))
    mutate('manifest-self-file', lambda m: m['files'].update({'RELEASE_MANIFEST.json': dict(row)}))
    mutate('manifest-self-directory', lambda m: m['directories'].update({'RELEASE_MANIFEST.json': {'mode': 493, 'mtime_ns': 1}}))
    mutate('file-directory-overlap', lambda m: m['directories'].update({'a/data.txt': {'mode': 493, 'mtime_ns': 1}}))
    mutate('empty-extra-directory', lambda m: m['directories'].update({'empty': {'mode': 493, 'mtime_ns': 1}}))
    mutate('missing-parent-directory', lambda m: m['directories'].clear())
    mutate('extra-entry-field', lambda m: m['files']['a/data.txt'].update({'extra': 1}))
    mutate('extra-top-field', lambda m: m.update({'extra': 1}))
    for field, value in [('mode', True), ('mode', 0o4755), ('mode', -1), ('mtime_ns', True), ('mtime_ns', -1), ('bytes', True), ('bytes', -1), ('sha256', 'A' * 64)]:
        mutate('invalid-' + field + '-' + str(value), lambda m, field=field, value=value: m['files']['a/data.txt'].update({field: value}))
    for label, m in mutations:
        rejects(label, lambda m=m: H['validate_manifest'](m))
    # Noncanonical roots/outputs and linked/special inputs.
    for raw in ('relative-output', str(O) + '/./out', str(O) + '/../out', str(O) + '//out', '//' + str(O).lstrip('/') + '/out'):
        rejects('reject-output-alias-' + raw, lambda raw=raw: H['new_output'](raw))
    rejects('reject-output-inside-candidate', lambda: H['new_output'](str(C / 'unwanted')))
    rejects('reject-output-inside-original', lambda: H['new_output']('/workspace/shared/two-witness-tensor-compiler-20261004/unwanted'))
    (O / 'alias').symlink_to(O, target_is_directory=True)
    rejects('reject-output-symlink-parent', lambda: H['new_output'](str(O / 'alias/out')))
    (O / 'dangling').symlink_to(O / 'missing')
    rejects('reject-existing-dangling-output', lambda: H['new_output'](str(O / 'dangling')))
    root = O / 'fs-probes'; root.mkdir(); (root / 'plain').write_bytes(b'inert')
    assert H['read'](root / 'plain') == b'inert'
    passed('read-valid-single-link-file')
    os.link(root / 'plain', O / 'outside-hardlink')
    rejects('reject-external-hardlink', lambda: H['read'](root / 'plain'))
    (O / 'outside-hardlink').unlink()
    (root / 'symlink').symlink_to(root / 'plain')
    rejects('reject-tree-symlink', lambda: H['inventory'](root))
    (root / 'symlink').unlink()
    (root / 'empty').mkdir()
    rejects('reject-empty-descendant', lambda: H['inventory'](root))
    (root / 'empty').rmdir()
    os.mkfifo(root / 'fifo')
    rejects('reject-fifo-read-without-open', lambda: H['read'](root / 'fifo'))
    rejects('reject-tree-fifo', lambda: H['inventory'](root))
    (root / 'fifo').unlink()
    RESULTS.append({'test': 'reject-tree-socket', 'status': 'NOT_RUN', 'reason': 'The original retained harness run established that this environment prohibits creating Unix sockets; no bypass attempted. FIFO and archived socket probes remain.'})
    cli('reject-nonisolated-interpreter', ['check-inputs'], isolated=False)
    # Every invalid archive must fail before creating its extraction root.
    good, good_pin = archive('valid-synthetic', manifest)
    valid_output = O / 'valid-extracted'
    cli('accept-valid-synthetic-extract', ['extract', '--archive', str(good), '--output-dir', str(valid_output), '--manifest-sha256', good_pin], success=True)
    assert (valid_output / 'a/data.txt').read_bytes() == b'Hello, Report69.\n'
    assert (valid_output / 'a/data.txt').stat().st_mtime_ns == row['mtime_ns']
    assert stat.S_IMODE((valid_output / 'a/data.txt').stat().st_mode) == row['mode']
    assert (valid_output / 'a').stat().st_mtime_ns == manifest['directories']['a']['mtime_ns']
    assert stat.S_IMODE(valid_output.stat().st_mode) == 0o700
    wrong_output = O / 'wrong-pin-output'
    cli('reject-externally-wrong-manifest-pin', ['extract', '--archive', str(good), '--output-dir', str(wrong_output), '--manifest-sha256', '0' * 64])
    assert not wrong_output.exists()
    transforms = {
        'duplicate-manifest': lambda x: [x[0], x[0], x[1]],
        'duplicate-payload': lambda x: [x[0], x[1], x[1]],
        'missing-payload': lambda x: x[:1],
        'missing-manifest': lambda x: x[1:],
        'wrong-member-order': lambda x: list(reversed(x)),
        'traversal-extra': lambda x: x + [('../escape.txt', b'escape', stat.S_IFREG | 0o644, 3)],
        'absolute-extra': lambda x: x + [('/escape.txt', b'escape', stat.S_IFREG | 0o644, 3)],
        'backslash-extra': lambda x: x + [('Report69/a\\escape.txt', b'escape', stat.S_IFREG | 0o644, 3)],
        'explicit-directory': lambda x: x + [('Report69/a/', b'', stat.S_IFDIR | 0o755, 3)],
        'symlink-payload': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFLNK | 0o640, 3)],
        'fifo-payload': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFIFO | 0o640, 3)],
        'socket-payload': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFSOCK | 0o640, 3)],
        'dos-payload': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFREG | 0o640, 0)],
        'changed-payload-mode': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFREG | 0o600, 3)],
        'setuid-payload-mode': lambda x: [x[0], (x[1][0], x[1][1], stat.S_IFREG | 0o4640, 3)],
        'symlink-manifest': lambda x: [(x[0][0], x[0][1], stat.S_IFLNK | 0o644, 3), x[1]],
    }
    for label, transform in transforms.items():
        reject_archive('zip-' + label, manifest, transform=transform)
    reject_archive('zip-payload-hash-tamper', manifest, content=b'Tampered, same archive CRC recomputed.\n')
    raw = enc(manifest).replace(b'"format":', b'"format":"wrong","format":')
    reject_archive('zip-duplicate-json-repinned', manifest, raw=raw)
    bad = copy.deepcopy(manifest)
    bad['files']['../outside'] = bad['files'].pop('a/data.txt'); bad['directories'].clear()
    reject_archive('zip-manifest-traversal-repinned', bad)
    for label, m in mutations:
        reject_archive('zip-schema-' + label, m)
    # Archive filesystem aliases never enter extraction.
    (O / 'archive-symlink.zip').symlink_to(good)
    cli('reject-archive-symlink', ['extract', '--archive', str(O / 'archive-symlink.zip'), '--output-dir', str(O / 'archive-symlink-out'), '--manifest-sha256', good_pin])
    os.link(good, O / 'archive-hardlink.zip')
    cli('reject-archive-hardlink', ['extract', '--archive', str(O / 'archive-hardlink.zip'), '--output-dir', str(O / 'archive-hardlink-out'), '--manifest-sha256', good_pin])
    (O / 'archive-hardlink.zip').unlink()
    # PNG validation exercises complete chunk ordering and bounded decompression.
    good_png = png()
    assert B['validate_png'](good_png, H['require']) == {'width': 1, 'height': 1}
    passed('valid-minimal-rgb-png')
    cases = {
        'bad-signature': b'BAD' + good_png[3:], 'truncation': good_png[:-1], 'trailing-data': good_png + b'junk',
        'zero-width': png(width=0), 'excess-width': png(width=10001), 'zero-height': png(height=0),
        'wrong-color': png(color=0), 'wrong-depth': png(depth=16), 'interlace': png(interlace=1),
        'unknown-chunk': png(before=chunk(b'tEXt', b'key\x00value')),
        'duplicate-header': png(before=chunk(b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 2, 0, 0, 0))),
        'physical-after-data': png(after=chunk(b'pHYs', struct.pack('>IIB', 120, 120, 1))),
        'zero-pixel-density': png(before=chunk(b'pHYs', struct.pack('>IIB', 0, 120, 1))),
        'duplicate-physical': png(before=chunk(b'pHYs', struct.pack('>IIB', 120, 120, 1)) * 2),
        'short-raster': png(pixels=b'\x00\x01'), 'long-raster': png(pixels=b'\x00' * 5),
        'invalid-row-filter': png(pixels=b'\x05\x11\x22\x33'),
        'compressed-trailer': png(stream=zlib.compress(b'\x00\x11\x22\x33') + b'junk'),
        'concatenated-zlib': png(stream=zlib.compress(b'\x00\x11\x22\x33') * 2),
        'incomplete-zlib': png(stream=zlib.compress(b'\x00\x11\x22\x33')[:-1]),
        'bad-crc': good_png[:45] + bytes([good_png[45] ^ 1]) + good_png[46:],
    }
    for label, data in cases.items():
        rejects('png-' + label, lambda data=data: B['validate_png'](data, H['require']))
    # Mutate only fresh external copies; independently re-sealing cannot bypass frozen pins.
    fixture = O / 'frozen-pin-map-fixture'
    shutil.copytree(C, fixture, copy_function=shutil.copy2)
    pins = json.loads((fixture / 'INPUT_PINS.json').read_bytes())
    pins['source_roots']['science/low-arity'] = '/untrusted/replacement'
    (fixture / 'INPUT_PINS.json').write_bytes(enc(pins))
    cli('reject-replaced-frozen-pin-map', ['check-inputs'], root=fixture)
    # Exact signed metadata: run against a complete independently sealed fixture.
    sealed = BASE / 'full-candidate-sealed'
    pin = sha((sealed / 'RELEASE_MANIFEST.json').read_bytes())
    changed = O / 'sealed-metadata-fixture'
    shutil.copytree(sealed, changed, copy_function=shutil.copy2)
    p = changed / 'README.md'; original = p.read_bytes(); original_stat = p.stat()
    def restore():
        p.write_bytes(original); p.chmod(stat.S_IMODE(original_stat.st_mode)); os.utime(p, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))
    p.chmod(stat.S_IMODE(original_stat.st_mode) ^ 0o100)
    cli('reject-sealed-file-mode-change', ['verify', '--manifest-sha256', pin], root=changed)
    restore(); os.utime(p, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns + 1))
    cli('reject-sealed-one-nanosecond-change', ['verify', '--manifest-sha256', pin], root=changed)
    restore(); p.write_bytes(original[:-1] + b'!'); os.utime(p, ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns))
    cli('reject-same-size-same-mtime-content-change', ['verify', '--manifest-sha256', pin], root=changed)
    restore(); directory = changed / 'manuscript'; ds = directory.stat(); directory.chmod(stat.S_IMODE(ds.st_mode) ^ 0o100)
    cli('reject-sealed-directory-mode-change', ['verify', '--manifest-sha256', pin], root=changed)
    directory.chmod(stat.S_IMODE(ds.st_mode)); os.utime(directory, ns=(ds.st_atime_ns, ds.st_mtime_ns + 1))
    cli('reject-sealed-directory-one-nanosecond-change', ['verify', '--manifest-sha256', pin], root=changed)
    os.utime(directory, ns=(ds.st_atime_ns, ds.st_mtime_ns))
    cli('accept-restored-complete-fixture', ['verify', '--manifest-sha256', pin], root=changed, success=True)
    receipt = {'status': 'PASS_WITH_ONE_ENVIRONMENT_LIMITATION', 'scope': 'Independent presentation-only synthetic/adversarial tests; no scientific executable', 'test_count': len(RESULTS), 'pass_count': sum(t['status'] == 'PASS' for t in RESULTS), 'not_run_count': sum(t['status'] == 'NOT_RUN' for t in RESULTS), 'tests': RESULTS}
    (BASE / 'ADVERSARIAL_RECEIPT.json').write_bytes(enc(receipt))
    print(enc(receipt).decode())

if __name__ == '__main__':
    main()
