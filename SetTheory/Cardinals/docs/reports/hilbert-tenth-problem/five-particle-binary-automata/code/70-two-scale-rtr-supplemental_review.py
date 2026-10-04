#!/usr/bin/env python3
"""Independent reference PNG decoder, source adaptation, and ZIP CRC review.
No scientific code is imported or executed.
"""
import difflib
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import struct
import subprocess
import sys
import zipfile
import zlib

BASE = Path('/workspace/shared/report70-independent-release-tool-review-20261004')
ROOT = BASE / 'reviewed-candidate'


def check(ok, why):
    if not ok:
        raise AssertionError(why)


def encode(x):
    return (json.dumps(x, sort_keys=True, indent=2) + '\n').encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def decode_png(data):
    check(data[:8] == b'\x89PNG\r\n\x1a\n', 'Signature')
    pos, chunks, payloads = 8, [], []
    while pos < len(data):
        n = int.from_bytes(data[pos:pos+4], 'big')
        kind, payload = data[pos+4:pos+8], data[pos+8:pos+8+n]
        crc = int.from_bytes(data[pos+8+n:pos+12+n], 'big')
        check(zlib.crc32(kind + payload) & 0xffffffff == crc, 'CRC')
        chunks.append(kind)
        if kind == b'IHDR':
            check(len(chunks) == 1, 'IHDR location')
            w, h, depth, color, compression, filtering, interlace = struct.unpack('>IIBBBBB', payload)
            check((depth, color, compression, filtering, interlace) == (8, 2, 0, 0, 0), 'Raster mode')
        elif kind == b'IDAT':
            payloads.append(payload)
        elif kind == b'IEND':
            check(n == 0, 'IEND payload')
        else:
            check(kind == b'pHYs', 'Unexpected chunk')
        pos += n + 12
    check(pos == len(data) and chunks[0] == b'IHDR' and chunks[-1] == b'IEND', 'Chunk boundaries')
    decoder = zlib.decompressobj()
    pixels = decoder.decompress(b''.join(payloads)) + decoder.flush()
    check(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail, 'Compressed-stream boundary')
    stride = 1 + 3*w
    check(len(pixels) == h*stride and all(pixels[i*stride] <= 4 for i in range(h)), 'Raster dimensions/filter')
    return {'width': w, 'height': h, 'sha256': digest(data), 'bytes': len(data), 'chunks': len(chunks)}


def main():
    check(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode, 'Use -I -S -B')
    primary = json.loads((BASE / 'INDEPENDENT_REVIEW_RECEIPT.json').read_bytes())
    check(primary['status'] == 'ACCEPTED', 'Primary review incomplete')
    results = []
    images = {}
    for build in ('direct-build', 'relocated-build'):
        pages = list(sorted((BASE / build / 'pages').glob('*.png')))
        check(len(pages) == 21, 'Page count')
        images[build] = {p.name: decode_png(p.read_bytes()) for p in pages}
    check(images['direct-build'] == images['relocated-build'], 'Independent decoded PNG inventories differ')
    results.append({'name': 'independent-reference-decode-all-42-pngs', 'status': 'PASS', 'png_count': 42})
    (BASE / 'INDEPENDENT_PNG_REFERENCE_VALIDATION.json').write_bytes(encode(images))

    # Establish that the fully read current implementation shares all remaining
    # source lines with both retained predecessors after the listed adaptation.
    diffs = []
    for old in (66, 68):
        for stem in ('release', 'build_report', 'selftest'):
            oldtext = (ROOT / f'qa/predecessor-contract/report{old}/tools/{stem}{old}.py').read_text()
            renamed = oldtext
            for prefix in ('Report', 'report', 'release', 'selftest'):
                renamed = renamed.replace(prefix + str(old), prefix + '70')
            current = (ROOT / f'tools/{stem}70.py').read_text()
            diff = ''.join(difflib.unified_diff(renamed.splitlines(True), current.splitlines(True), fromfile=f'{stem}{old}-report-identity-normalized', tofile=f'{stem}70'))
            diffs.append(diff)
            if stem == 'release':
                allowed = ('INPUT_PINS_SHA256 =', 'MODULES =', 'PROTECTED =')
                normalize = lambda t: '\n'.join(line for line in t.splitlines() if not line.startswith(allowed))
                check(normalize(renamed) == normalize(current), 'Unexpected release adaptation')
            elif stem == 'build_report':
                normalize = lambda t: '\n'.join(line for line in t.splitlines() if not line.startswith('HELPER_SHA256 ='))
                check(normalize(renamed) == normalize(current), 'Unexpected build adaptation')
            else:
                fixture = 'science/bounded-certificates' if old == 66 else 'science/counting'
                check(renamed.replace(fixture, 'science/proof-packet') == current, 'Unexpected selftest adaptation')
    (BASE / 'INDEPENDENT_PREDECESSOR_DIFF.txt').write_text('\n'.join(diffs))
    results.append({'name': 'independently-confirm-predecessor-adaptation', 'status': 'PASS', 'retained_predecessor_sources_compared': 6})

    pins = json.loads((ROOT / 'INPUT_PINS.json').read_bytes())
    directories = {}
    for rel, expected in pins['directories'].items():
        matching = [k for k, v in pins['source_roots'].items() if Path(v).is_dir() and (rel == k or rel.startswith(k + '/'))]
        if not matching:
            continue  # Presentation-created grouping directories have no original counterpart.
        check(len(matching) == 1, 'Directory source mapping ambiguity')
        key = matching[0]
        source = Path(pins['source_roots'][key]) if rel == key else Path(pins['source_roots'][key]) / rel[len(key)+1:]
        s = source.lstat()
        check({'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns} == expected, 'Original directory metadata differs')
        directories[rel] = {'source': str(source), **expected}
    (BASE / 'ORIGINAL_DIRECTORIES_VERIFIED.json').write_bytes(encode(directories))
    results.append({'name': 'original-mapped-directory-metadata', 'status': 'PASS', 'directories': len(directories)})

    # Corrupt a ZIP_STORED member without updating either CRC; it must be refused
    # before extraction creates an output tree, despite an authentic manifest.
    source = BASE / 'archives/documented-container-metadata-boundary.zip'
    data = bytearray(source.read_bytes())
    with zipfile.ZipFile(source) as z:
        info = z.getinfo('Report70/README.md')
        check(info.compress_type == zipfile.ZIP_STORED, 'Fixture compression')
        off = info.header_offset
        name_len, extra_len = struct.unpack('<HH', data[off+26:off+30])
        payload_offset = off + 30 + name_len + extra_len
    data[payload_offset] ^= 1
    corrupt = BASE / 'archives/corrupt-crc.zip'
    corrupt.write_bytes(data)
    out = BASE / 'outputs/crc-rejection'
    cp = subprocess.run([sys.executable, '-I', '-S', '-B', str(ROOT / 'tools/release70.py'), 'extract', '--archive', str(corrupt), '--output-dir', str(out), '--manifest-sha256', primary['candidate_manifest_sha256']], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    (BASE / 'logs/reject-archive-raw-crc.txt').write_bytes(cp.stdout)
    check(cp.returncode == 2 and b'ZIP CRC failure' in cp.stdout and not os.path.lexists(out), 'Raw CRC corruption not rejected before writing')
    results.append({'name': 'reject-archive-raw-crc-before-writing', 'status': 'PASS', 'outcome': 'rejected'})

    receipt = {'status': 'ACCEPTED', 'scope': 'Supplemental independent presentation-only checks', 'test_count': len(results), 'tests': results}
    (BASE / 'SUPPLEMENTAL_REVIEW_RECEIPT.json').write_bytes(encode(receipt))
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
