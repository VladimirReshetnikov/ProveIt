#!/usr/bin/env python3
"""Independent presentation-only Report70 release audit.
Only the fully read Report70 release/build/selftest tools and fresh synthetic TeX
are executed. Scientific, archived and predecessor programs remain inert bytes.
No network, uploads, original-source mutation or scientific execution occurs.
"""
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

BASE = Path('/workspace/shared/report70-independent-release-tool-review-20261004')
ORIGINAL = Path('/workspace/shared/report70-two-scale-radius-release-20261004')
CANDIDATE = BASE / 'reviewed-candidate'
MANIFEST = 'RELEASE_MANIFEST.json'
PINS = '944b95cbd26caf7bca3967fc8be0c4395b9fd5df3e517fe953767c39cdaf0332'
LOCK = 'a467e715df8470d46d66d94e64da543bf3aaf4a5e2192cc486ddaf98d913df9c'
PDF = 'd061fda50f26cad711e4f20d028d126d1ce232469425b0745728eed014895010'
SOURCE_PINS = {
    'INPUT_PINS.json': '5c3f393080392a5bdbd1fb1f8d12ce005f87d4f8a34715a20a07a652af0bcbee',
    'tools/release70.py': '701d67bddd82ee531c9000981430729bfd47f595f1e980423bff10191583a589',
    'tools/build_report70.py': 'a4e6a84fa8c89e154eb35c70ed077c07f3d65da632d3c1b898c3712c27989c07',
    'tools/selftest70.py': '0653e6455dc80d6fcb3d6eef297ca7e8da7d1ae9d9d566b858d2a0d2eaa2cbe4',
    'tools/BUILD_DEPENDENCIES_LOCK.json': LOCK,
    'manuscript/MANUSCRIPT_PINS.json': PINS,
    'Report70.pdf': PDF,
}
RESULTS = []


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def encode(obj):
    return (json.dumps(obj, sort_keys=True, indent=2) + '\n').encode()


def save(name, obj):
    (BASE / name).write_bytes(encode(obj))


def file_row(path, identity=False):
    s = path.lstat()
    check(stat.S_ISREG(s.st_mode) and s.st_nlink == 1, 'Not an independent regular file: ' + str(path))
    row = {'bytes': s.st_size, 'sha256': sha(path.read_bytes()), 'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
    if identity:
        row.update(dev=s.st_dev, inode=s.st_ino, ctime_ns=s.st_ctime_ns, nlink=s.st_nlink)
    return row


def tree(root):
    files, directories = {}, {}
    for p in sorted(root.rglob('*')):
        rel = p.relative_to(root).as_posix()
        s = p.lstat()
        if stat.S_ISDIR(s.st_mode):
            directories[rel] = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        else:
            files[rel] = file_row(p)
    s = root.lstat()
    return {'files': files, 'directories': directories, 'root': {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}}


def passed(name, **detail):
    RESULTS.append({'name': name, 'status': 'PASS', **detail})
    save('PROGRESS.json', {'completed': len(RESULTS), 'tests': RESULTS})
    print(name, flush=True)


def command(name, tool, args, root=CANDIDATE, accept=True, reason=None, absent=None, env=None, flags=None):
    argv = [sys.executable, *(flags if flags is not None else ['-I', '-S', '-B']), str(root / 'tools' / tool), *map(str, args)]
    result = subprocess.run(argv, cwd=BASE, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=420)
    (BASE / 'logs' / (name + '.txt')).write_bytes(result.stdout)
    check((result.returncode == 0) == accept, name + ': unexpected exit: ' + result.stdout.decode(errors='replace')[-5000:])
    if reason:
        check(reason.encode() in result.stdout, name + ': wrong rejection reason: ' + result.stdout.decode(errors='replace')[-5000:])
    if absent is not None:
        check(not os.path.lexists(absent), name + ': rejected output was created')
    passed(name, outcome='accepted' if accept else 'rejected', returncode=result.returncode,
           command=argv, log='logs/' + name + '.txt', expected_reason=reason)
    return result


def clone(name, source=CANDIDATE):
    out = BASE / 'mutants' / name
    shutil.copytree(source, out, copy_function=shutil.copy2)
    return out


def reject_verify(name, mutate, reason='Release inventory, bytes, mode or mtime mismatch'):
    root = clone(name)
    mutate(root)
    command(name, 'release70.py', ['verify', '--manifest-sha256', MANIFEST_PIN], root, False, reason)


def reject_input(name, mutate, reason):
    root = clone(name)
    mutate(root)
    command(name, 'release70.py', ['check-inputs'], root, False, reason)


def png_chunk(kind, payload):
    return struct.pack('>I', len(payload)) + kind + payload + struct.pack('>I', zlib.crc32(kind + payload) & 0xffffffff)


def png(width=1, height=1, raster=b'\0\1\2\3', depth=8, color=2, interlace=0, extra=b'', compressed=None):
    ihdr = struct.pack('>IIBBBBB', width, height, depth, color, 0, 0, interlace)
    return b'\x89PNG\r\n\x1a\n' + png_chunk(b'IHDR', ihdr) + extra + png_chunk(b'IDAT', zlib.compress(raster) if compressed is None else compressed) + png_chunk(b'IEND', b'')


def build_checks(name, output, baseline=None):
    receipt = json.loads((output / 'BUILD_RECEIPT.json').read_bytes())
    check(receipt['status'] == 'PASS' and receipt['dependency_lock_verified'] and receipt['packaged_pdf_match'], name + ': incomplete locked claim')
    check(sha((output / 'Report70.pdf').read_bytes()) == PDF, name + ': wrong PDF')
    check((output / 'BUILD_DEPENDENCIES.json').read_bytes() == (CANDIDATE / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes(), 'Postflight lock mismatch')
    check((output / 'PRESERVATION_BEFORE.json').read_bytes() == (output / 'PRESERVATION_AFTER.json').read_bytes(), 'Build preservation mismatch')
    inventory = json.loads((output / 'PAGE_INVENTORY.json').read_bytes())
    check(len(inventory) == 21 and {p.name for p in (output / 'pages').iterdir()} == set(inventory), 'Page inventory mismatch')
    for name_, row in inventory.items():
        data = (output / 'pages' / name_).read_bytes()
        check(sha(data) == row['sha256'] and len(data) == row['bytes'], 'Page hash mismatch')
        check(VALIDATE_PNG(data, check) == {k: row[k] for k in ('width', 'height')}, 'Page raster mismatch')
        if baseline:
            check(data == (baseline / 'pages' / name_).read_bytes(), 'PNG differs: ' + name_)
    union = json.loads((output / 'RECORDER_INPUT_UNION.json').read_bytes())
    check([r['pass'] for r in union['passes']] == ['format', 'compile-1', 'compile-2', 'compile-3'], 'Pass list mismatch')
    recorded = set()
    for item in union['passes']:
        data = (output / (item['pass'] + '.fls')).read_bytes()
        check(sha(data) == item['fls_sha256'], 'Recorder hash mismatch')
        system = set()
        for line in data.decode().splitlines():
            if line.startswith('INPUT '):
                p = Path(line[6:])
                if p.is_absolute() and not str(p).startswith(str(output) + '/'):
                    system.add(str(p.resolve(strict=True)))
        check(system == set(item['system_inputs']), 'Independent recorder interpretation mismatch')
        recorded |= system
    for filename in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
        p = Path((output / ('map-' + filename + '.stdout')).read_text().strip()).resolve(strict=True)
        recorded.add(str(p))
    check(recorded == set(union['union']), 'Union omitted or added inputs')
    for path, row in union['union'].items():
        data = Path(path).read_bytes()
        check(row == {'bytes': len(data), 'sha256': sha(data)}, 'Current dependency differs')
    passed(name, pdf_sha256=PDF, png_count=len(inventory), all_passes_and_selected_maps=True,
           recorder_union_count=len(recorded), all_pngs_equal_to=str(baseline) if baseline else None)


def archive_variant(name, transform=None, extra=None, reorder=False, remove=None, container=False):
    target = BASE / 'archives' / (name + '.zip')
    with zipfile.ZipFile(BASE / 'candidate-a.zip') as src, zipfile.ZipFile(target, 'w') as dst:
        items = src.infolist()
        if reorder:
            items = list(reversed(items))
        for original in items:
            info = copy.copy(original)
            data = src.read(original)
            if original.filename == remove:
                continue
            if transform:
                info, data = transform(info, data)
            if container:
                info.date_time = (2001, 2, 3, 4, 5, 6)
                info.comment = b'unauthenticated member comment'
                info.compress_type = zipfile.ZIP_STORED
                if info.filename.endswith('/' + MANIFEST):
                    info.external_attr = (stat.S_IFREG | 0o600) << 16
            dst.writestr(info, data)
        if extra:
            dst.writestr(*extra)
        if container:
            dst.comment = b'unauthenticated container comment'
    return target


def reject_archive(name, archive, reason, pin=None):
    target = BASE / 'outputs' / name
    command(name, 'release70.py', ['extract', '--archive', archive, '--output-dir', target, '--manifest-sha256', pin or MANIFEST_PIN],
            accept=False, reason=reason, absent=target)


def main():
    global MANIFEST_PIN, VALIDATE_PNG
    check(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode, 'Run -I -S -B')
    for name in ('logs', 'mutants', 'archives', 'outputs'):
        (BASE / name).mkdir()
    for name, expected in SOURCE_PINS.items():
        check(sha((ORIGINAL / name).read_bytes()) == expected, 'Supplied pin mismatch: ' + name)
    save('INSPECTED_SOURCE_PINS.json', SOURCE_PINS)
    before_copy = tree(ORIGINAL)
    shutil.copytree(ORIGINAL, CANDIDATE, copy_function=shutil.copy2)
    check(tree(CANDIDATE) == before_copy, 'Metadata preserving candidate copy failed')
    save('CANDIDATE_UNSEALED_SNAPSHOT.json', before_copy)
    passed('metadata-preserving-external-copy', files=len(before_copy['files']), directories=len(before_copy['directories']))

    pins = json.loads((CANDIDATE / 'INPUT_PINS.json').read_bytes())
    origins = json.loads((CANDIDATE / 'qa/SOURCE_ORIGINS.json').read_bytes())
    check(origins == pins['source_roots'], 'Original mapping disagreement')
    original_before = {}
    original_mapping = {}
    for rel, expected in pins['files'].items():
        matching = [k for k in origins if rel == k or rel.startswith(k + '/')]
        check(len(matching) == 1, 'Ambiguous original mapping')
        key = matching[0]
        source = Path(origins[key]) / rel[len(key) + 1:] if rel != key else Path(origins[key])
        check(file_row(source) == expected == file_row(CANDIDATE / rel), 'Original file differs: ' + rel)
        original_before[str(source)] = file_row(source, True)
        original_mapping[rel] = {'source': str(source), **expected}
    check(len(original_mapping) == 45, 'Wrong copied original count')
    save('ORIGINAL_45_FILES_VERIFIED.json', {'status': 'PASS', 'count': 45, 'files': original_mapping})
    save('ORIGINAL_IDENTITIES_BEFORE.json', original_before)
    passed('independent-original-mapping-verification', count=45, fields=['bytes', 'sha256', 'mode', 'mtime_ns'])

    # The following imports execute only previously fully inspected presentation tools.
    helper = runpy.run_path(str(CANDIDATE / 'tools/release70.py'), run_name='independent_release_validation')
    builder = runpy.run_path(str(CANDIDATE / 'tools/build_report70.py'), run_name='independent_png_validation')
    VALIDATE_PNG = builder['validate_png']
    command('candidate-fixed-input-authentication', 'release70.py', ['check-inputs'])
    command('candidate-deterministic-flatten', 'release70.py', ['prepare', '--output-dir', BASE / 'prepared'])
    check((BASE / 'prepared/Report70.tex').read_bytes() == (CANDIDATE / 'Report70.tex').read_bytes(), 'Flattened manuscript differs')
    check(sha((BASE / 'prepared/MANUSCRIPT_PINS.json').read_bytes()) == PINS, 'Flattened pins differ')
    passed('flattened-tex-and-manuscript-map-equality')

    command('candidate-manifest-generation', 'release70.py', ['manifest', '--output', BASE / 'candidate-manifest.json'])
    shutil.copy2(BASE / 'candidate-manifest.json', CANDIDATE / MANIFEST)
    MANIFEST_PIN = sha((BASE / 'candidate-manifest.json').read_bytes())
    manifest = json.loads((CANDIDATE / MANIFEST).read_bytes())
    sealed = tree(CANDIDATE)
    save('SEALED_CANDIDATE_SNAPSHOT.json', sealed)
    actual = {k: dict(sealed[k]) for k in ('files', 'directories')}
    del actual['files'][MANIFEST]
    check(actual == {k: manifest[k] for k in ('files', 'directories')}, 'Independent manifest inventory mismatch')
    check(set(manifest) == {'format', 'files', 'directories'}, 'Unexpected root inventory')
    passed('exact-descendant-inventory', files=len(manifest['files']), directories=len(manifest['directories']), manifest_sha256=MANIFEST_PIN)
    command('candidate-external-manifest-verification', 'release70.py', ['verify', '--manifest-sha256', MANIFEST_PIN])
    common = ['--pins-sha', PINS, '--dependency-lock-sha', LOCK, '--require-packaged-match']
    command('direct-locked-packaged-build', 'build_report70.py', [*common, '--output-dir', BASE / 'direct-build'])
    build_checks('direct-pdf-png-recorder-and-preservation-equality', BASE / 'direct-build', Path('/workspace/shared/report70-locked-replay-v5-20261004'))

    for name, args, reason in [
        ('no-isolation', [], 'Use python3 -I -S -B'),
        ('missing-no-site', ['-I', '-B'], 'Use python3 -I -S -B'),
        ('missing-no-bytecode', ['-I', '-S'], 'Use python3 -I -S -B'),
        ('optimization', ['-I', '-S', '-B', '-O'], 'without optimization')]:
        command('reject-' + name, 'release70.py', ['check-inputs'], accept=False, reason=reason, flags=args)
    for name, path, reason in [
        ('relative-output', 'relative-new', 'Canonical absolute output'),
        ('double-slash-output', '//' + str(BASE).lstrip('/') + '/bad', 'Canonical absolute output'),
        ('dotdot-output', str(BASE) + '/../bad', 'Output path alias'),
        ('dot-output', str(BASE) + '/./bad', 'Canonical absolute output'),
        ('existing-output', str(BASE / 'prepared'), 'Output must be fresh'),
        ('source-overlap', str(CANDIDATE / 'bad'), 'Output overlaps protected input'),
        ('protected-original-overlap', '/workspace/shared/radius-frontier-20261004/bad-independent-review', 'Output overlaps protected input'),
        ('protected-report68-overlap', '/workspace/shared/report68-gap-statistics-release-20261004/bad-independent-review', 'Output overlaps protected input'),
        ('protected-report66-overlap', '/workspace/shared/report66-bounded-certificates-counting-release-20261004/bad-independent-review', 'Output overlaps protected input'),
    ]:
        command('reject-' + name, 'release70.py', ['prepare', '--output-dir', path], accept=False, reason=reason)
    (BASE / 'alias').symlink_to(BASE, target_is_directory=True)
    command('reject-output-symlink-parent', 'release70.py', ['prepare', '--output-dir', BASE / 'alias/alias-output'], accept=False, reason='Symlink path component')
    (BASE / 'source-alias').symlink_to(CANDIDATE, target_is_directory=True)
    command('reject-source-symlink-parent', 'release70.py', ['check-inputs'], root=BASE / 'source-alias', accept=False, reason='Symlink path component')
    (BASE / 'broken-output').symlink_to(BASE / 'absent')
    command('reject-dangling-output', 'release70.py', ['prepare', '--output-dir', BASE / 'broken-output'], accept=False, reason='Output must be fresh')
    for label, pin in [('wrong', '0' * 64), ('uppercase', MANIFEST_PIN.upper()), ('short', 'abc')]:
        command('reject-' + label + '-manifest-pin', 'release70.py', ['verify', '--manifest-sha256', pin], accept=False,
                reason='Manifest digest mismatch' if label == 'wrong' else 'Expected lowercase SHA-256 pin')
    for label, args, reason in [
        ('wrong-manuscript-pin', ['--pins-sha', '0' * 64, '--bootstrap'], 'Manuscript pin map does not match external pin'),
        ('wrong-lock-pin', ['--pins-sha', PINS, '--dependency-lock-sha', '0' * 64], 'Dependency lock differs from external pin'),
        ('low-render-dpi', [*common, '--render-dpi', '71'], 'Render DPI'),
        ('high-render-dpi', [*common, '--render-dpi', '201'], 'Render DPI')]:
        out = BASE / 'outputs' / label
        command('reject-' + label, 'build_report70.py', [*args, '--output-dir', out], accept=False, reason=reason, absent=out)

    reject_input('reject-fixed-pin-map-reformat', lambda r: (r / 'INPUT_PINS.json').write_text(json.dumps(pins)), 'Frozen input-pin map differs')
    def repin_changed_source(r):
        p = r / 'science/proof-packet/PROOF.md'
        p.write_bytes(p.read_bytes() + b'\n% changed inert scientific text\n')
        altered = copy.deepcopy(pins)
        altered['files']['science/proof-packet/PROOF.md'] = file_row(p)
        (r / 'INPUT_PINS.json').write_bytes(encode(altered))
    reject_input('reject-repinned-scientific-source', repin_changed_source, 'Frozen input-pin map differs')
    reject_input('reject-source-content', lambda r: (r / 'science/proof-packet/PROOF.md').write_bytes(b'tampered inert bytes'), 'Frozen input inventory')
    reject_input('reject-frozen-mode', lambda r: (r / 'science/proof-packet/PROOF.md').chmod(0o600), 'Frozen input inventory')
    def nudge(p):
        s = p.stat(); os.utime(p, ns=(s.st_atime_ns, s.st_mtime_ns + 1))
    reject_input('reject-frozen-nanosecond-mtime', lambda r: nudge(r / 'science/proof-packet/PROOF.md'), 'Frozen input inventory')
    reject_input('reject-frozen-directory-mode', lambda r: (r / 'science/proof-packet').chmod(0o700), 'Frozen input inventory')
    reject_input('reject-frozen-root-mtime', lambda r: nudge(r / 'science'), 'Frozen scope root metadata differs')
    reject_input('reject-added-frozen-file', lambda r: (r / 'science/proof-packet/unexpected').write_text('inert'), 'Frozen input inventory')
    reject_verify('reject-unlisted-file', lambda r: (r / 'qa/unlisted.txt').write_text('inert'))
    reject_verify('reject-missing-file', lambda r: (r / 'README.md').unlink())
    reject_verify('reject-unlisted-empty-directory', lambda r: (r / 'empty').mkdir(), 'Unexpected empty directory')
    reject_verify('reject-descendant-directory-mtime', lambda r: nudge(r / 'qa'))
    reject_verify('reject-descendant-directory-mode', lambda r: (r / 'qa').chmod(0o700))
    reject_verify('reject-hardlink', lambda r: os.link(r / 'README.md', r / 'alias.txt'), 'Expected single-link regular file')
    reject_verify('reject-symlink', lambda r: (r / 'alias.txt').symlink_to(r / 'README.md'), 'Nonregular tree entry')
    reject_verify('reject-fifo', lambda r: os.mkfifo(r / 'fifo'), 'Nonregular tree entry')
    reject_verify('reject-manifest-byte-tamper', lambda r: (r / MANIFEST).write_bytes((r / MANIFEST).read_bytes() + b' '), 'Manifest digest mismatch')
    # The README explicitly excludes manifest filesystem metadata and release root metadata.
    boundary = clone('documented-root-manifest-metadata-boundary')
    boundary.chmod(0o700); nudge(boundary)
    (boundary / MANIFEST).chmod(0o600); nudge(boundary / MANIFEST)
    boundary_before = tree(boundary)
    command('accept-documented-root-manifest-metadata-boundary', 'release70.py', ['verify', '--manifest-sha256', MANIFEST_PIN], boundary)
    check(tree(boundary) == boundary_before, 'Boundary verify mutated root')

    # Independently generated PNG adversaries, including valid CRC but invalid raster.
    check(VALIDATE_PNG(png(), check) == {'width': 1, 'height': 1}, 'Valid RGB PNG rejected')
    passed('accept-independent-valid-png')
    bad_pngs = {
        'signature': b'bad', 'truncation': png()[:-1], 'trailing': png() + b'bad',
        'zero-width': png(width=0), 'oversize': png(width=10001), 'depth': png(depth=16),
        'color': png(color=6), 'interlace': png(interlace=1), 'short-raster': png(raster=b'\0\1\2'),
        'long-raster': png(raster=b'\0\1\2\3\4'), 'row-filter': png(raster=b'\5\1\2\3'),
        'compressed-trailer': png(compressed=zlib.compress(b'\0\1\2\3') + b'x'),
        'incomplete-zlib': png(compressed=zlib.compress(b'\0\1\2\3')[:-1]),
        'unknown-chunk': png(extra=png_chunk(b'tEXt', b'x')),
        'zero-density': png(extra=png_chunk(b'pHYs', struct.pack('>IIB', 0, 1, 1))),
        'duplicate-ihdr': png(extra=png_chunk(b'IHDR', struct.pack('>IIBBBBB', 1, 1, 8, 2, 0, 0, 0))),
    }
    bad = bytearray(png()); bad[45] ^= 1; bad_pngs['crc'] = bytes(bad)
    for name, data in bad_pngs.items():
        try:
            VALIDATE_PNG(data, check)
        except (AssertionError, zlib.error):
            passed('reject-png-' + name, outcome='rejected')
        else:
            raise AssertionError('PNG accepted: ' + name)

    for label, mutate in [
        ('path-traversal', lambda m: m['files'].__setitem__('../evil', next(iter(m['files'].values())))),
        ('absolute-path', lambda m: m['files'].__setitem__('/evil', next(iter(m['files'].values())))),
        ('self-reference', lambda m: m['files'].__setitem__(MANIFEST, next(iter(m['files'].values())))),
        ('file-directory-overlap', lambda m: m['directories'].__setitem__('README.md', {'mode': 0o755, 'mtime_ns': 1})),
        ('empty-directory', lambda m: m['directories'].__setitem__('empty', {'mode': 0o755, 'mtime_ns': 1})),
        ('special-mode', lambda m: m['files']['README.md'].__setitem__('mode', 0o4755)),
        ('boolean-size', lambda m: m['files']['README.md'].__setitem__('bytes', True)),
        ('negative-mtime', lambda m: m['files']['README.md'].__setitem__('mtime_ns', -1)),
    ]:
        altered = copy.deepcopy(manifest); mutate(altered)
        try:
            helper['validate_manifest'](altered)
        except ValueError:
            passed('reject-manifest-schema-' + label, outcome='rejected')
        else:
            raise AssertionError('Manifest schema accepted: ' + label)
    try:
        helper['parse'](b'{"x":1,"x":2}')
    except ValueError:
        passed('reject-duplicate-json-keys', outcome='rejected')
    else:
        raise AssertionError('Duplicate keys accepted')

    for suffix in ('a', 'b'):
        command('deterministic-candidate-archive-' + suffix, 'release70.py', ['archive', '--manifest-sha256', MANIFEST_PIN, '--output', BASE / ('candidate-' + suffix + '.zip')])
    a = (BASE / 'candidate-a.zip').read_bytes(); b = (BASE / 'candidate-b.zip').read_bytes()
    check(a == b, 'Archive bytes differ')
    with zipfile.ZipFile(BASE / 'candidate-a.zip') as archive:
        check(archive.namelist() == ['Report70/' + n for n in sorted([*manifest['files'], MANIFEST])], 'ZIP descendants differ')
        check(all(i.date_time == (2026, 10, 4, 0, 0, 0) and i.compress_type == zipfile.ZIP_DEFLATED for i in archive.infolist()), 'ZIP deterministic metadata differs')
    passed('repeated-complete-zip-byte-equality', archive_sha256=sha(a), bytes=len(a))
    command('safe-authenticated-extraction', 'release70.py', ['extract', '--archive', BASE / 'candidate-a.zip', '--output-dir', BASE / 'relocated', '--manifest-sha256', MANIFEST_PIN])
    relocated = tree(BASE / 'relocated')
    check({k: {n: r for n, r in relocated[k].items() if n != MANIFEST} for k in ('files', 'directories')} == actual, 'Relocated inventory differs')
    check(relocated['root']['mode'] == 0o700 and relocated['files'][MANIFEST]['mode'] == 0o644 and relocated['files'][MANIFEST]['mtime_ns'] == 1791072000000000000, 'Extraction boundary metadata incorrect')
    passed('restored-every-descendant-byte-mode-nanosecond-mtime', files=len(actual['files']), directories=len(actual['directories']))
    command('relocated-external-manifest-verification', 'release70.py', ['verify', '--manifest-sha256', MANIFEST_PIN], root=BASE / 'relocated')
    command('relocated-locked-packaged-build', 'build_report70.py', [*common, '--output-dir', BASE / 'relocated-build'], root=BASE / 'relocated')
    build_checks('relocated-pdf-and-every-png-equality', BASE / 'relocated-build', BASE / 'direct-build')
    check(tree(BASE / 'relocated') == relocated, 'Relocated build changed extracted tree')

    reject_archive('reject-archive-wrong-pin', BASE / 'candidate-a.zip', 'Archived manifest pin mismatch', '0' * 64)
    reject_archive('reject-archive-traversal', archive_variant('traversal', extra=('../escape', b'bad')), 'Archive inventory mismatch')
    reject_archive('reject-archive-absolute', archive_variant('absolute', extra=('/tmp/escape', b'bad')), 'Archive inventory mismatch')
    reject_archive('reject-archive-duplicate', archive_variant('duplicate', extra=('Report70/README.md', b'bad')), 'Archive inventory mismatch')
    reject_archive('reject-archive-reordered', archive_variant('reordered', reorder=True), 'Archive inventory mismatch')
    reject_archive('reject-archive-missing-member', archive_variant('missing', remove='Report70/README.md'), 'Archive inventory mismatch')
    def payload_change(info, data):
        return info, data + b'bad' if info.filename == 'Report70/README.md' else data
    reject_archive('reject-archive-payload-tamper', archive_variant('payload', payload_change), 'Archived bytes differ')
    def mode_change(info, data):
        if info.filename == 'Report70/README.md':
            info.external_attr = (stat.S_IFREG | 0o600) << 16
        return info, data
    reject_archive('reject-archive-mode-tamper', archive_variant('mode', mode_change), 'Archived mode differs')
    def symlink_change(info, data):
        if info.filename == 'Report70/README.md':
            info.external_attr = (stat.S_IFLNK | 0o777) << 16
        return info, data
    reject_archive('reject-archive-symlink-entry', archive_variant('symlink', symlink_change), 'Nonregular ZIP entry')
    def creator_change(info, data):
        if info.filename == 'Report70/README.md':
            info.create_system = 0
        return info, data
    reject_archive('reject-archive-nonunix-entry', archive_variant('nonunix', creator_change), 'Nonregular ZIP entry')
    # Authenticated JSON still has to satisfy structural constraints.
    duplicate_raw = (CANDIDATE / MANIFEST).read_bytes().replace(b'{', b'{"format":"duplicate",', 1)
    def manifest_change(info, data):
        return info, duplicate_raw if info.filename == 'Report70/' + MANIFEST else data
    reject_archive('reject-authenticated-duplicate-manifest-key', archive_variant('duplicate-json', manifest_change), 'Duplicate JSON key', sha(duplicate_raw))
    container = archive_variant('documented-container-metadata-boundary', container=True)
    command('accept-documented-container-metadata-boundary', 'release70.py', ['extract', '--archive', container, '--output-dir', BASE / 'container-boundary-copy', '--manifest-sha256', MANIFEST_PIN])
    command('verify-container-boundary-copy', 'release70.py', ['verify', '--manifest-sha256', MANIFEST_PIN], root=BASE / 'container-boundary-copy')

    # Re-run all inspected owned selftests as a separate, explicitly owned receipt.
    command('reproduce-39-owned-selftests', 'selftest70.py', ['--output-dir', BASE / 'owned-selftests'])
    owned = json.loads((BASE / 'owned-selftests/SELFTEST_RECEIPT.json').read_bytes())
    check(owned['test_count'] == 39 and all(t['status'] == 'PASS' for t in owned['tests']), 'Owned selftest receipt differs')

    # Independent synthetic bootstrap/locked/hostile tests use freshly authored TeX.
    synthetic = clone('independent-synthetic')
    (synthetic / MANIFEST).unlink()
    modules = helper['MODULES']
    for name in modules[1:]:
        (synthetic / 'manuscript' / name).write_text('% Independent synthetic presentation fixture\n')
    text = ('\\documentclass{article}\n\\IfFileExists{Report70.aux}{}{\\usepackage{ifthen}}\n'
            '\\pdfinfoomitdate=1\n\\pdftrailerid{}\n\\begin{document}\nIndependent presentation fixture.\n' +
            ''.join('\\input{manuscript/' + n + '}\n' for n in modules[1:]) + '\\end{document}\n')
    (synthetic / 'manuscript/Report70.tex').write_text(text)
    command('independent-synthetic-prepare', 'release70.py', ['prepare', '--output-dir', BASE / 'synthetic-prepared'], synthetic)
    shutil.copy2(BASE / 'synthetic-prepared/Report70.tex', synthetic / 'Report70.tex')
    shutil.copy2(BASE / 'synthetic-prepared/MANUSCRIPT_PINS.json', synthetic / 'manuscript/MANUSCRIPT_PINS.json')
    spin = sha((synthetic / 'manuscript/MANUSCRIPT_PINS.json').read_bytes())
    command('independent-synthetic-bootstrap', 'build_report70.py', ['--pins-sha', spin, '--bootstrap', '--output-dir', BASE / 'synthetic-bootstrap'], synthetic)
    br = json.loads((BASE / 'synthetic-bootstrap/BUILD_RECEIPT.json').read_bytes())
    pf = json.loads((BASE / 'synthetic-bootstrap/PREFLIGHT.json').read_bytes())
    check(br['status'] == pf['status'] == 'BOOTSTRAP' and br['dependency_lock_verified'] is False and pf['dependency_lock_sha256'] is None, 'Bootstrap overstated verification')
    passed('bootstrap-explicitly-not-preflight-verified')
    slock = (BASE / 'synthetic-bootstrap/BUILD_DEPENDENCIES.json').read_bytes()
    shutil.copy2(BASE / 'synthetic-bootstrap/BUILD_DEPENDENCIES.json', synthetic / 'tools/BUILD_DEPENDENCIES_LOCK.json')
    shutil.copy2(BASE / 'synthetic-bootstrap/Report70.pdf', synthetic / 'Report70.pdf')
    sc = ['--pins-sha', spin, '--dependency-lock-sha', sha(slock), '--require-packaged-match']
    union = json.loads((BASE / 'synthetic-bootstrap/RECORDER_INPUT_UNION.json').read_bytes())
    first_only = set(union['passes'][1]['system_inputs']) - set(union['passes'][3]['system_inputs'])
    early = [p for p in first_only if p.endswith('/ifthen.sty')]
    check(len(early) == 1 and early[0] in union['union'], 'First-pass-only dependency lost')
    format_only = set(union['passes'][0]['system_inputs']) - set().union(*(set(p['system_inputs']) for p in union['passes'][1:]))
    check(format_only and format_only <= set(union['union']), 'Format-only dependencies lost')
    passed('independent-first-pass-and-format-only-dependencies-retained', first_pass_only=early, format_only_count=len(format_only))
    for key in ('TMPDIR', 'TEMP', 'TMP'):
        env = os.environ.copy()
        for k in ('TMPDIR', 'TEMP', 'TMP'):
            env.pop(k, None)
        env[key] = str(synthetic / 'science/proof-packet')
        env.update(TEXINPUTS=str(synthetic / 'science'), TEXMFHOME=str(synthetic / 'audits'), TEXMFVAR=str(synthetic / 'science'), TEXFORMATS=str(synthetic / 'science'))
        before = tree(synthetic)
        command('independent-hostile-' + key.lower(), 'build_report70.py', [*sc, '--output-dir', BASE / ('synthetic-hostile-' + key.lower())], synthetic, env=env)
        check(tree(synthetic) == before, 'Hostile environment changed inputs')
        check((BASE / ('synthetic-hostile-' + key.lower()) / 'Report70.pdf').read_bytes() == (synthetic / 'Report70.pdf').read_bytes(), 'Hostile build PDF differs')
    for label, alter, reason, preflight in [
        ('omitted-first-pass', lambda d: d['system_inputs'].pop(early[0]), 'Unpinned or changed executed TeX input', False),
        ('omitted-format', lambda d: d['system_inputs'].pop(sorted(format_only)[0]), 'Unpinned or changed executed TeX input', False),
        ('stale-system', lambda d: d['system_inputs'][early[0]].__setitem__('sha256', '0' * 64), 'System-input preflight mismatch', True),
        ('stale-executable', lambda d: d['executables']['pdftex'].__setitem__('sha256', '0' * 64), 'Executable preflight mismatch', True),
    ]:
        target = clone('synthetic-' + label, synthetic)
        altered = json.loads(slock); alter(altered); data = encode(altered)
        (target / 'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data)
        output = BASE / 'outputs' / ('synthetic-' + label)
        before = tree(target)
        command('reject-independent-' + label, 'build_report70.py', ['--pins-sha', spin, '--dependency-lock-sha', sha(data), '--output-dir', output],
                target, False, reason, absent=output if preflight else None)
        check(tree(target) == before, 'Rejected build changed input')
        if not preflight:
            failure = json.loads((output / 'BUILD_FAILURE.json').read_bytes())
            check(failure['release_preserved'] is True and failure['status'] == 'FAIL', 'Failure preservation not recorded')
    target = clone('changed-helper', synthetic)
    p = target / 'tools/release70.py'; p.write_bytes(p.read_bytes() + b'\n# inert modification\n')
    command('reject-changed-helper', 'build_report70.py', [*sc, '--output-dir', BASE / 'outputs/changed-helper'], target, False, 'Release helper differs from inspected source', absent=BASE / 'outputs/changed-helper')

    check(tree(CANDIDATE) == sealed, 'Sealed candidate changed during review')
    check({path: file_row(Path(path), True) for path in original_before} == original_before, 'Original sources changed during review')
    save('ORIGINAL_IDENTITIES_AFTER.json', {path: file_row(Path(path), True) for path in original_before})
    for rel, expected in SOURCE_PINS.items():
        check(sha((ORIGINAL / rel).read_bytes()) == expected, 'Main frozen source changed: ' + rel)
    passed('all-45-original-files-and-sealed-candidate-preserved')
    final = {'status': 'ACCEPTED', 'scope': 'Independent presentation-only tool and candidate-workflow review; no scientific executable run or scientific theorem re-proved',
             'candidate': str(CANDIDATE), 'candidate_manifest_sha256': MANIFEST_PIN, 'archive_sha256': sha(a), 'pdf_sha256': PDF,
             'test_count': len(RESULTS), 'tests': RESULTS, 'owned_tests_reproduced_separately': 39,
             'original_files_verified': 45, 'direct_and_relocated_pdf_equal': True, 'every_rendered_png_equal': True, 'page_count': 21,
             'all_original_files_preserved_including_identity': True, 'sealed_candidate_preserved': True,
             'boundaries': ['Manifest bytes authenticated only by externally supplied digest; manifest filesystem metadata and release-root mode/mtime excluded',
                            'Descendant inventory, file bytes/size/mode/mtime and directory mode/mtime are authenticated exactly',
                            'ZIP container timestamps/comments/compression not authenticated by extraction; creator/type and file modes are checked',
                            'Toolchain lock omits shared libraries, Python standard library and operating system',
                            'Bootstrap records dependencies and explicitly does not claim preflight verification',
                            'Static review and successful typesetting do not establish mathematical correctness',
                            'Candidate snapshot excludes final independent review dossiers to be added by the parent before final sealing']}
    save('INDEPENDENT_REVIEW_RECEIPT.json', final)
    print(json.dumps({k: v for k, v in final.items() if k != 'tests'}, indent=2), flush=True)


if __name__ == '__main__':
    main()
