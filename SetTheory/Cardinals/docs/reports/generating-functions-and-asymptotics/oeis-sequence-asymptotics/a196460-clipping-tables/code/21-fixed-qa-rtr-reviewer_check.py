#!/usr/bin/env python3
"""Independent presentation-only audit. Scientific files are read as inert bytes only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import subprocess
import sys
import zlib
import zipfile

ORIGINAL = Path('/workspace/shared/oeis-arity-asymptotics-release-20261004')
OUT = Path(__file__).absolute().parent
PIN = 'f330e99fd48b98ce57b1b205416d98acda22dbff63ca6ab2c0a769919120250d'
LOCK = '01477b108b9576ce8fe0fc3ee516e1c106e684940d335a6fe694c675e5e60f79'
PDF = '2a95d839ec43787f55cd73a7cb8e6a65635210388398f33b30396910cc128910'
TEX = '6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c'
TOOLS = {'release.py': '2515d07ae3a5136f89d9beeedab51fc7302ddba5db5124ace774e46d89a3f0a4',
         'build_article.py': '35302b6e247dc27e4f1d87d107feb4d6b748513e72222a782ecb3a5ee4bbfb2e',
         'freeze_inputs.py': 'c44db716e024f2ebae44ec65f57be067615c81397c047c6546041e0a431b2cb5',
         'selftest.py': 'b08cb95a06ce8d496c423defe0dbf755ca9e50b60f52047ebbb55bbda86033f6'}

def need(ok, why):
    if not ok:
        raise ValueError(why)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def enc(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()

def load(path):
    def unique(pairs):
        answer = {}
        for k, v in pairs:
            need(k not in answer, 'Duplicate JSON key')
            answer[k] = v
        return answer
    return json.loads(path.read_bytes(), object_pairs_hook=unique)

def row(path, size=False):
    s = path.lstat()
    need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Nonregular entry: ' + str(path))
    r = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
    if size:
        r.update(kind=stat.S_IFMT(s.st_mode), size=s.st_size)
    if stat.S_ISREG(s.st_mode):
        need(s.st_nlink == 1, 'Hardlinked entry')
        data = path.read_bytes()
        r.update(sha256=sha(data))
        if not size:
            r['bytes'] = len(data)
    return r

def tree(root):
    need(not root.is_symlink(), 'Symlink tree root')
    files, dirs = {}, {}
    for p in sorted(root.rglob('*')):
        r = row(p)
        target = dirs if p.is_dir() else files
        target[p.relative_to(root).as_posix()] = r
    return {'root': row(root), 'files': files, 'directories': dirs}

def run(root, tool, args, label, expected=0):
    argv = [sys.executable, '-I', '-S', '-B', str(root / 'tools' / tool), *args]
    result = subprocess.run(argv, cwd=OUT, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=600)
    (OUT / (label + '.stdout')).write_bytes(result.stdout)
    need(result.returncode == expected, label + ' failed: ' + result.stdout.decode(errors='replace')[-3000:])
    commands.append({'label': label, 'argv': argv, 'exit_status': result.returncode})
    print(label + ': PASS', flush=True)
    return result

def png(data):
    need(data[:8] == b'\x89PNG\r\n\x1a\n', 'PNG signature')
    pos, seen, chunks = 8, [], []
    while pos < len(data):
        need(pos + 12 <= len(data), 'PNG truncation')
        n, kind = struct.unpack('>I4s', data[pos:pos + 8])
        body = data[pos + 8:pos + 8 + n]
        end = pos + 12 + n
        need(end <= len(data), 'PNG payload truncation')
        crc = struct.unpack('>I', data[pos + 8 + n:end])[0]
        need(zlib.crc32(kind + body) & 0xffffffff == crc, 'PNG checksum')
        seen.append(kind)
        if kind == b'IHDR':
            width, height, depth, color, comp, filt, inter = struct.unpack('>IIBBBBB', body)
            need((depth, color, comp, filt, inter) == (8, 2, 0, 0, 0), 'Unexpected PNG format')
        elif kind == b'IDAT':
            chunks.append(body)
        elif kind == b'IEND':
            need(n == 0 and end == len(data), 'PNG trailer')
        pos = end
    need(seen[0] == b'IHDR' and seen[-1] == b'IEND', 'PNG chunk ordering')
    pixels = zlib.decompress(b''.join(chunks))
    need(len(pixels) == height * (width * 3 + 1), 'PNG full raster size')
    need(all(pixels[y * (width * 3 + 1)] <= 4 for y in range(height)), 'PNG row filters')
    return {'width': width, 'height': height, 'bytes': len(data), 'sha256': sha(data)}

def independent_inputs(root):
    pins = load(root / 'INPUT_PINS.json')
    need(sha((root / 'INPUT_PINS.json').read_bytes()) == 'a831a8433e0c85cd108df9a5f559428069ba8cec8cf302d2569087c5b63ccadb', 'Frozen input pin')
    actual = tree(root / 'inputs')
    need(pins['roots'] == {'inputs': actual['root']}, 'Input root metadata')
    for kind in ('files', 'directories'):
        need(pins[kind] == {'inputs/' + k: v for k, v in actual[kind].items()}, 'Frozen input ' + kind)
    for name, mpin in [('asymptotics', '6ae30398c52b6fe1d07a91346791ed3355e7104c55b19a4103de257299293de1'),
                       ('independent-audit', '737af333985bc079ecdd688f1854f7221bb86169db7841d91a1115d2f94e7055')]:
        scope = root / 'inputs' / name
        source = Path(pins['source_roots'][name])
        need(tree(scope) == tree(source), 'Source copy bytes/modes/mtime mismatch')
        data = (scope / 'MANIFEST.sha256').read_bytes()
        need(sha(data) == mpin, 'Source manifest pin')
        records = {line[66:]: line[:64] for line in data.decode().splitlines()}
        files = tree(scope)['files']
        need(set(files) == set(records) | {'MANIFEST.sha256'}, 'Manifest exact payload inventory')
        need(all(files[k]['sha256'] == v for k, v in records.items()), 'Source manifest payload pin')
    deps = load(root / 'qa/tool-closure-dependency-pins.json')
    for name, v in deps.items():
        r = dict(v); source = Path(r.pop('origin'))
        need(row(source, True) == r == row(root / 'inputs/closure-dependencies' / name, True), 'Closure dependency pin/metadata')
    histories = root / 'inputs/asymptotics/evidence'
    second = root / 'inputs/independent-audit/original-history'
    for name in ('input-before.json', 'input-current.json', 'input-changes.json', 'core-final.json', 'preservation-result.json', 'preservation.log'):
        need((histories / name).read_bytes() == (second / name).read_bytes(), 'Historical evidence differs')
    before, after, changes, core = [load(histories / name) for name in ('input-before.json', 'input-current.json', 'input-changes.json', 'core-final.json')]
    diff = {k: {'before': before.get(k), 'after': after.get(k)} for k in set(before) | set(after) if before.get(k) != after.get(k)}
    need(diff == changes and len(changes) == 132 and len(before) == 249 and len(after) == 376, 'Authentic historical difference set')
    counts = {name: sum(k == '/workspace/shared/' + name or k.startswith('/workspace/shared/' + name + '/') for k in changes)
              for name in ('report69-low-arity-compilers-release-20261004', 'report70-two-scale-radius-release-20261004')}
    need(list(counts.values()) == [44, 88], 'Historical difference scope')
    need(len(core) == 62 and all(before[k] == after[k] == v == row(Path(k), True) for k, v in core.items()), 'Unchanged 62-entry historical core')
    original = load(root / 'qa/tool-original-inputs-before.json')
    need(len(original) == 994 and all(row(Path(k), True) == v for k, v in original.items()), 'Fresh 994-entry original inventory')
    return {'frozen_files': len(actual['files']), 'history_before': len(before), 'history_after': len(after),
            'historical_changes': 132, 'counts': counts, 'unchanged_core': 62, 'original_scoped_entries': 994}

commands = []
def main():
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode, 'Run isolated Python')
    candidate = OUT / 'candidate'
    baseline = tree(ORIGINAL)
    need(not candidate.exists(), 'Fresh candidate required')
    shutil.copytree(ORIGINAL, candidate, copy_function=shutil.copy2)
    need(tree(candidate) == baseline == tree(ORIGINAL), 'Metadata-preserving stable snapshot failed')
    (OUT / 'CANDIDATE_BEFORE.json').write_bytes(enc(baseline))
    for name, pin in TOOLS.items():
        need(sha((candidate / 'tools' / name).read_bytes()) == pin, 'Inspected tool source changed')
    need(sha((candidate / 'article.tex').read_bytes()) == TEX and (candidate / 'article.tex').read_bytes() == (candidate / 'manuscript/article.tex').read_bytes(), 'Manuscript source')
    need(sha((candidate / 'article.pdf').read_bytes()) == PDF, 'Accepted PDF pin')
    need(sha((candidate / 'manuscript/MANUSCRIPT_PINS.json').read_bytes()) == PIN, 'Manuscript external pin')
    need(sha((candidate / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()) == LOCK, 'Dependency external pin')
    inputs = independent_inputs(candidate)
    run(candidate, 'release.py', ['check-inputs'], 'input-authentication')
    run(candidate, 'freeze_inputs.py', ['verify-originals'], 'original-preservation')
    common = ['--pins-sha', PIN, '--dependency-lock-sha', LOCK, '--require-packaged-match']
    build = OUT / 'locked-build'
    run(candidate, 'build_article.py', common + ['--output-dir', str(build)], 'locked-build')
    need(sha((build / 'article.pdf').read_bytes()) == PDF, 'Locked PDF deterministic equality')
    need((build / 'BUILD_DEPENDENCIES.json').read_bytes() == (candidate / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes(), 'Exact dependency lock receipt')
    lock = load(candidate / 'tools/BUILD_DEPENDENCIES_LOCK.json')
    union = load(build / 'RECORDER_INPUT_UNION.json')
    need(union['union'] == lock['system_inputs'] and len(union['passes']) == 4, 'Four-pass exact lock union')
    for p, v in lock['system_inputs'].items():
        data = Path(p).read_bytes(); need({'bytes': len(data), 'sha256': sha(data)} == v, 'Locked system bytes changed')
    maps = []
    for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
        maps.append((build / ('map-' + name + '.stdout')).read_text().strip())
    need(set(lock['system_inputs']) == set(maps).union(*(set(p['system_inputs']) for p in union['passes'])), 'Independent union recomputation')
    rendered = {p.name: png(p.read_bytes()) for p in sorted((build / 'pages').iterdir())}
    need(len(rendered) == 16 and rendered == load(build / 'PAGE_INVENTORY.json') == load(candidate / 'qa/tool-build-initial/PAGE_INVENTORY.json'), 'All 16 complete rasters deterministic equality')
    need(load(build / 'PRESERVATION_BEFORE.json') == load(build / 'PRESERVATION_AFTER.json'), 'Build preservation receipt')
    run(candidate, 'selftest.py', ['--output-dir', str(OUT / 'owned-selftests')], 'owned-selftests')
    owned = load(OUT / 'owned-selftests/SELFTEST_RECEIPT.json')
    need(owned['test_count'] == 39 and all(t['status'] == 'PASS' for t in owned['tests']), 'Owned tests count')
    manifest_path = OUT / 'candidate-manifest.json'
    run(candidate, 'release.py', ['manifest', '--output', str(manifest_path)], 'manifest-generation')
    shutil.copy2(manifest_path, candidate / 'RELEASE_MANIFEST.json')
    manifest = load(manifest_path); mpin = sha(manifest_path.read_bytes())
    run(candidate, 'release.py', ['verify', '--manifest-sha256', mpin], 'manifest-verification')
    for suffix in ('a', 'b'):
        run(candidate, 'release.py', ['archive', '--manifest-sha256', mpin, '--output', str(OUT / ('release-' + suffix + '.zip'))], 'archive-' + suffix)
    archive = OUT / 'release-a.zip'
    need(archive.read_bytes() == (OUT / 'release-b.zip').read_bytes(), 'Repeated whole archive equality')
    extracted = OUT / 'extracted'
    run(candidate, 'release.py', ['extract', '--manifest-sha256', mpin, '--archive', str(archive), '--output-dir', str(extracted)], 'extraction')
    restored = tree(extracted)
    restored['files'].pop('RELEASE_MANIFEST.json')
    need(all(restored[k] == manifest[k] for k in ('files', 'directories')), 'Independent bytes/modes/nanosecond restoration')
    run(extracted, 'release.py', ['verify', '--manifest-sha256', mpin], 'relocated-verification')
    relocated = OUT / 'relocated-build'
    run(extracted, 'build_article.py', common + ['--output-dir', str(relocated)], 'relocated-locked-build')
    need((relocated / 'article.pdf').read_bytes() == (build / 'article.pdf').read_bytes(), 'Relocated PDF equality')
    need(load(relocated / 'PAGE_INVENTORY.json') == rendered, 'Relocated 16-raster equality')
    with zipfile.ZipFile(archive) as z:
        payload = [(info, z.read(info)) for info in z.infolist()]
    for kind in ('extra', 'duplicate', 'symlink', 'wrong-mode', 'corrupt-payload'):
        bad = OUT / ('bad-' + kind + '.zip')
        with zipfile.ZipFile(bad, 'w', compression=zipfile.ZIP_DEFLATED) as z:
            for old, data in payload:
                info = zipfile.ZipInfo(old.filename, old.date_time)
                info.create_system = old.create_system; info.external_attr = old.external_attr
                if old.filename == 'ArityAsymptotics/README.md':
                    if kind == 'symlink': info.external_attr = (stat.S_IFLNK | 0o644) << 16
                    if kind == 'wrong-mode': info.external_attr ^= 0o100 << 16
                    if kind == 'corrupt-payload': data += b'tamper'
                z.writestr(info, data)
            if kind == 'extra': z.writestr('../escape.txt', b'blocked')
            if kind == 'duplicate': z.writestr(payload[0][0], payload[0][1])
        dest = OUT / ('bad-output-' + kind)
        run(candidate, 'release.py', ['extract', '--manifest-sha256', mpin, '--archive', str(bad), '--output-dir', str(dest)], 'reject-archive-' + kind, 2)
        need(not dest.exists(), 'Malformed archive created output')
    independent_inputs(candidate)
    need(tree(ORIGINAL) == baseline, 'Original candidate changed during review')
    (OUT / 'ORIGINAL_AFTER.json').write_bytes(enc(tree(ORIGINAL)))
    result = {'status': 'PASS', 'candidate_tex_sha256': TEX, 'candidate_pdf_sha256': PDF,
              'input_pins_sha256': 'a831a8433e0c85cd108df9a5f559428069ba8cec8cf302d2569087c5b63ccadb',
              'manuscript_pins_sha256': PIN, 'dependency_lock_sha256': LOCK,
              'source_tools': TOOLS, 'inputs': inputs, 'dependency_system_input_count': len(lock['system_inputs']),
              'owned_selftest_count': 39, 'additional_archive_refusal_count': 5, 'page_count': 16,
              'pdf_and_all_rasters_equal_across_relocated_locked_builds': True,
              'candidate_snapshot_manifest_sha256': mpin, 'repeated_zip_sha256': sha(archive.read_bytes()),
              'original_candidate_preserved': True, 'scientific_execution': False,
              'scope': 'Presentation and release tooling only. No scientific artifacts imported or executed. Candidate snapshot, not final release seal.',
              'commands': commands}
    (OUT / 'REVIEW_RECEIPT.json').write_bytes(enc(result))
    print(enc(result).decode())

if __name__ == '__main__':
    main()
