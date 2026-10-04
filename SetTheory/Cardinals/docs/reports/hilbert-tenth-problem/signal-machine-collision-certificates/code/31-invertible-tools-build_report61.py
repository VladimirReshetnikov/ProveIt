#!/usr/bin/env python3
"""Typeset the owned Report61 manuscript in an isolated fresh TeX workspace.
Use python3 -I -S -B tools/build_report61.py --pins-sha SHA --dependency-lock-sha SHA --output-dir /fresh/external/directory
Only installed TeX/Poppler binaries run; no frozen scientific program is executed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import struct
import zlib
import subprocess
import sys
import tempfile

ROOT = Path(__file__).absolute().parent.parent
MODULES = ('Report61.tex', 'results.tex', 'geometry.tex', 'reversal.tex', 'realization.tex', 'evidence.tex')
SYSTEM_ROOTS = ('/usr/share/texlive/', '/usr/share/texmf/', '/etc/texmf/', '/var/lib/texmf/')

def require(test, message):
    if not test:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()

def read(path):
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode) and before.st_nlink == 1, 'Expected single-link regular file: ' + str(path))
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as f:
        opened = os.fstat(f.fileno())
        data = f.read()
        after = os.fstat(f.fileno())
    final = path.lstat()
    def sig(s):
        return (s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    require(sig(before) == sig(opened) == sig(after) == sig(final), 'Concurrent input change')
    return data

def inventory():
    return full_inventory()

def output_path(raw):
    p = Path(raw)
    require(raw.startswith('/') and not raw.startswith('//') and str(p) == raw, 'Canonical absolute output required')
    require('..' not in p.parts and '.' not in p.parts, 'Path alias')
    require(not os.path.lexists(p), 'Output must be fresh')
    require(p.parent == p.parent.resolve(strict=True), 'Output parent must be real and canonical')
    require(ROOT not in p.parents and p not in ROOT.parents, 'Output overlaps release')
    return p

def run(argv, cwd, env, timeout=240):
    p = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    require(p.returncode == 0, 'Command failed: ' + argv[0] + '\n' + p.stdout.decode(errors='replace')[-6000:])
    return p.stdout


DEPENDENCY_SCOPE = 'Executed binary bytes and recorded TeX/font-map inputs; dynamic libraries not inventoried'

def validate_png(data):
    require(data.startswith(b'\x89PNG\r\n\x1a\n'), 'Invalid PNG signature')
    offset = 8
    chunks = []
    compressed = []
    width = height = None
    while offset < len(data):
        require(offset + 12 <= len(data), 'Truncated PNG chunk')
        length = struct.unpack('>I', data[offset:offset+4])[0]
        kind = data[offset+4:offset+8]
        end = offset + 12 + length
        require(end <= len(data), 'Truncated PNG payload')
        payload = data[offset+8:offset+8+length]
        require(zlib.crc32(kind + payload) & 0xffffffff == struct.unpack('>I', data[offset+8+length:end])[0], 'PNG CRC mismatch')
        require(kind in (b'IHDR', b'IDAT', b'IEND', b'pHYs'), 'Unexpected PNG chunk')
        if kind == b'IHDR':
            require(not chunks and length == 13, 'Invalid PNG header')
            width, height, depth, color, compression, filtering, interlace = struct.unpack('>IIBBBBB', payload)
            require(0 < width <= 10000 and 0 < height <= 10000 and (depth, color, compression, filtering, interlace) == (8, 2, 0, 0, 0), 'Invalid rendered PNG format')
        if kind == b'pHYs':
            require(chunks and chunks[-1] == b'IHDR' and b'pHYs' not in chunks and length == 9, 'Invalid PNG physical-dimensions chunk')
            x_density, y_density, unit = struct.unpack('>IIB', payload)
            require(x_density > 0 and y_density > 0 and unit in (0, 1), 'Invalid PNG physical dimensions')
        if kind == b'IDAT':
            require(chunks and chunks[-1] in (b'IHDR', b'pHYs', b'IDAT'), 'Invalid PNG data order')
            compressed.append(payload)
        if kind == b'IEND':
            require(length == 0 and end == len(data), 'Invalid PNG end')
        chunks.append(kind)
        offset = end
    require(chunks and chunks[0] == b'IHDR' and chunks[-1] == b'IEND' and compressed, 'Incomplete PNG')
    decoder = zlib.decompressobj()
    expected = height * (1 + width * 3)
    pixels = decoder.decompress(b''.join(compressed), expected + 1)
    require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail and len(pixels) == expected, 'Invalid PNG compressed raster')
    require(all(pixels[row * (1 + width * 3)] <= 4 for row in range(height)), 'Invalid PNG row filter')
    return width, height


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
    parser.add_argument('--pins-sha', required=True)
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--require-packaged-match', action='store_true')
    parser.add_argument('--bootstrap-dependencies', action='store_true', help='Explicit unlocked first build; emits only a dependency receipt')
    parser.add_argument('--dependency-lock-sha')
    args = parser.parse_args()
    require(re.fullmatch(r'[0-9a-f]{64}', args.pins_sha), 'Invalid pin digest')
    before = inventory()
    check_frozen(before)
    if (ROOT / 'RELEASE_MANIFEST.json').exists():
        check_manifest()
    raw_pins = read(ROOT / 'manuscript' / 'MANUSCRIPT_PINS.json')
    require(sha(raw_pins) == args.pins_sha, 'Manuscript pin-file digest mismatch')
    pins = parse(raw_pins)
    require(isinstance(pins, dict) and all(row_valid(row) for row in pins.values()), 'Invalid manuscript pin schema')
    require(set(pins) == set(MODULES), 'Unexpected module pins')
    require(set(p.name for p in (ROOT / 'manuscript').iterdir()) == set(MODULES) | {'MANUSCRIPT_PINS.json'}, 'Unexpected manuscript entries')
    sources = {name: read(ROOT / 'manuscript' / name) for name in MODULES}
    require(all(pins[name] == {'bytes': len(data), 'sha256': sha(data)} for name, data in sources.items()), 'Module pin mismatch')
    flat = sources['Report61.tex']
    for name in MODULES[1:]:
        token = ('\\input{' + name + '}\n').encode()
        require(flat.count(token) == 1, 'Unexpected module input count')
        flat = flat.replace(token, sources[name])
    require(flat == read(ROOT / 'Report61.tex'), 'Standalone and modular TeX differ')
    require(re.search(rb'\\(?:input|include)\b', flat) is None, 'Unresolved manuscript input')
    out = output_path(args.output_dir)
    binaries = {}
    for name in ('pdftex', 'pdflatex', 'kpsewhich', 'pdftotext', 'pdftoppm', 'pdfinfo'):
        path = Path('/usr/bin', name).resolve(strict=True)
        binaries[name] = {'path': str(path), 'sha256': sha(read(path))}
    lock_path = ROOT / 'tools' / 'BUILD_DEPENDENCIES_LOCK.json'
    require(not (args.bootstrap_dependencies and args.dependency_lock_sha), 'Bootstrap and lock pin are mutually exclusive')
    lock = None
    if args.bootstrap_dependencies:
        require(not lock_path.exists(), 'Bootstrap refuses an existing dependency lock')
    else:
        require(args.dependency_lock_sha and re.fullmatch(r'[0-9a-f]{64}', args.dependency_lock_sha), 'A dependency lock SHA-256 is required')
        lock_raw = read(lock_path)
        require(sha(lock_raw) == args.dependency_lock_sha, 'Dependency lock digest mismatch')
        lock = parse(lock_raw)
        require(isinstance(lock, dict) and set(lock) == {'executables', 'system_inputs', 'scope'} and lock['scope'] == DEPENDENCY_SCOPE, 'Invalid dependency lock schema')
        require(lock['executables'] == binaries, 'Executable preflight lock mismatch')
        require(isinstance(lock['system_inputs'], dict) and lock['system_inputs'], 'Empty or invalid dependency lock inputs')
        for filename, row in lock['system_inputs'].items():
            require(row_valid(row), 'Invalid dependency lock input row')
            path = Path(filename)
            require(str(path) == filename and path.is_absolute() and path == path.resolve(strict=True) and any(filename.startswith(base) for base in SYSTEM_ROOTS), 'Invalid dependency lock path')
            data = read(path)
            require(row == {'sha256': sha(data), 'bytes': len(data)}, 'Dependency preflight lock mismatch: ' + filename)
    out.mkdir(mode=0o700)
    system = {}
    with tempfile.TemporaryDirectory(prefix='report61-typeset-', dir='/tmp') as temp:
        work = Path(temp)
        cache = work / 'cache'
        home = work / 'home'
        cache.mkdir()
        home.mkdir()
        (work / 'Report61.tex').write_bytes(flat)
        env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'TZ': 'UTC', 'HOME': str(home),
               'SOURCE_DATE_EPOCH': '1791072000', 'FORCE_SOURCE_DATE': '1',
               'TEXMF': '{/usr/share/texlive/texmf-dist,/usr/share/texmf}', 'TEXMFVAR': str(cache), 'TEXMFCONFIG': str(cache),
               'TEXMFHOME': str(home), 'TEXFORMATS': str(cache) + ':', 'openin_any': 'p', 'openout_any': 'p',
               'shell_escape': 'f', 'MKTEXPK': '0', 'MKTEXTFM': '0', 'MKTEXMF': '0'}
        log = run(['/usr/bin/pdftex', '-ini', '-etex', '-no-shell-escape', '-recorder', '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'], cache, env)
        (out / 'format.log').write_bytes(log)
        def record_system(path):
            path = path.resolve(strict=True)
            require(any(str(path).startswith(base) for base in SYSTEM_ROOTS), 'Unexpected external TeX input: ' + str(path))
            data = read(path)
            row = {'sha256': sha(data), 'bytes': len(data)}
            require(str(path) not in system or system[str(path)] == row, 'TeX input changed between observations')
            system[str(path)] = row
            return data
        def record_inputs(recorder, base):
            for line in read(recorder).decode().splitlines():
                if line.startswith('INPUT '):
                    p = Path(line[6:])
                    p = (p if p.is_absolute() else base / p).resolve(strict=True)
                    if work not in p.parents:
                        record_system(p)
        record_inputs(cache / 'pdflatex.fls', cache)
        maps = []
        for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
            value = run(['/usr/bin/kpsewhich', name], work, env, 30).decode().strip()
            require(value and '\n' not in value, 'Missing or ambiguous font map')
            maps.append(record_system(Path(value)))
        (cache / 'pdftex.map').write_bytes(b'\n'.join(maps) + b'\n')
        env['TEXFONTMAPS'] = str(cache) + ':'
        for pass_number in range(1, 4):
            log = run(['/usr/bin/pdflatex', '-no-shell-escape', '-recorder', '-halt-on-error', '-interaction=nonstopmode', '-file-line-error', 'Report61.tex'], work, env)
            (out / ('compile-' + str(pass_number) + '.log')).write_bytes(log)
            record_inputs(work / 'Report61.fls', work)
        warning_terms = (b'Overfull \\hbox', b'Overfull \\vbox', b'undefined references', b'undefined citations', b'Rerun to get cross-references right', b'Label(s) may have changed', b'rerunfilecheck Warning')
        warnings = [term.decode() for term in warning_terms if term in log]
        (out / 'LAYOUT_STATUS.json').write_bytes(encoded({'blocking_warnings': warnings}))
        require(lock is None or system == lock['system_inputs'], 'Post-build dependency set differs from preflight lock')
        for filename, row in system.items():
            data = read(Path(filename))
            require(row == {'sha256': sha(data), 'bytes': len(data)}, 'TeX input changed during build')
        pdf = read(work / 'Report61.pdf')
        require(pdf.startswith(b'%PDF-'), 'Invalid PDF signature')
        match = (ROOT / 'Report61.pdf').exists() and read(ROOT / 'Report61.pdf') == pdf
        require(not args.require_packaged_match or match, 'Packaged PDF differs')
        (out / 'Report61.pdf').write_bytes(pdf)
        (out / 'Report61.log').write_bytes(read(work / 'Report61.log'))
        run(['/usr/bin/pdftotext', '-layout', str(out / 'Report61.pdf'), str(out / 'Report61.txt')], work, env)
        info = run(['/usr/bin/pdfinfo', str(out / 'Report61.pdf')], work, env)
        (out / 'pdfinfo.txt').write_bytes(info)
        found = re.search(rb'^Pages:\s+([1-9][0-9]*)\s*$', info, re.M)
        require(found is not None, 'PDF page count absent')
        count = int(found.group(1))
        pages = out / 'pages'
        pages.mkdir()
        run(['/usr/bin/pdftoppm', '-r', '120', '-png', str(out / 'Report61.pdf'), str(pages / 'page')], work, env)
        images = sorted(pages.iterdir())
        require(len(images) == count, 'Page render count mismatch')
        numbers = []
        for p in images:
            m = re.fullmatch(r'page-([0-9]+)\.png', p.name)
            require(m is not None, 'Invalid page render name')
            validate_png(read(p))
            numbers.append(int(m.group(1)))
        require(sorted(numbers) == list(range(1, count + 1)), 'Rendered page sequence mismatch')
    for name, row in binaries.items():
        path = Path('/usr/bin', name).resolve(strict=True)
        require({'path': str(path), 'sha256': sha(read(path))} == row, 'Executable changed during build')
    after = inventory()
    require(before == after, 'Source release changed during build')
    dependencies = {'executables': binaries, 'system_inputs': system, 'scope': DEPENDENCY_SCOPE}
    (out / 'BUILD_DEPENDENCIES.json').write_bytes(encoded(dependencies))
    receipt = {'report': 61, 'status': 'PASS' if not warnings else 'FAIL', 'toolchain_lock_verified': lock is not None, 'dependency_lock_sha256': args.dependency_lock_sha, 'png_integrity_verified': True, 'fresh_format': True, 'shell_escape': False, 'pdf_sha256': sha(pdf), 'source_sha256': sha(flat), 'pins_sha256': args.pins_sha,
               'pages': count, 'render_dpi': 120, 'packaged_match': match, 'blocking_warnings': warnings,
               'source_preserved': True, 'executed_scientific_programs': [],
               'build_tool_sha256': sha(read(Path(__file__).absolute()))}
    (out / 'BUILD_RECEIPT.json').write_bytes(encoded(receipt))
    print(encoded(receipt).decode(), end='')
    require(not warnings, 'Final PDF has blocking layout/reference warnings; inspect outputs and revise')

if __name__ == '__main__':
    main()
