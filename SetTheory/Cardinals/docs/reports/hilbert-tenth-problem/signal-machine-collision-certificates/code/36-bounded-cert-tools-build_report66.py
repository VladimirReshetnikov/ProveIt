#!/usr/bin/env python3
"""Build Report66 with an isolated fresh TeX format and all-pass dependency recording.
Use python3 -I -S -B, an external manuscript pin, and either --bootstrap or an
external --dependency-lock-sha. Bootstrap records dependencies; it does not claim
preflight lock verification. No scientific constructor/checker is executed.
"""
import argparse
import hashlib
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import sys
import tempfile
import types
import zlib

ROOT = Path(__file__).absolute().parent.parent
HELPER_SHA256 = '6a86de64d934a9bf13a3780edf7ef92942d72a860146b442ad89949606360344'
SYSTEM_ROOTS = ('/usr/share/texlive/', '/usr/share/texmf/', '/etc/texmf/', '/var/lib/texmf/')
SCOPE = 'Interpreter and executable bytes plus union of every format/TeX-pass recorder input and selected font maps; shared libraries, Python standard library and operating system are not inventoried'
EPOCH = '1791072000'


def load_helper():
    p = ROOT / 'tools/release66.py'
    for parent in [p, *p.parents]:
        if stat.S_ISLNK(parent.lstat().st_mode):
            raise ValueError('Symlink helper path')
    s = p.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('Helper is not a single-link regular file')
    with os.fdopen(os.open(p, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as f:
        data = f.read()
    if hashlib.sha256(data).hexdigest() != HELPER_SHA256:
        raise ValueError('Release helper differs from inspected source')
    module = types.ModuleType('report66_release')
    module.__file__ = str(p)
    exec(compile(data, str(p), 'exec'), module.__dict__)
    return module


def validate_png(data, require):
    require(data[:8] == b'\x89PNG\r\n\x1a\n', 'Invalid PNG signature')
    offset, chunks, compressed = 8, [], []
    width = height = 0
    while offset < len(data):
        require(offset + 12 <= len(data), 'Truncated PNG chunk')
        length = struct.unpack('>I', data[offset:offset + 4])[0]
        kind = data[offset + 4:offset + 8]
        end = offset + 12 + length
        require(end <= len(data), 'Truncated PNG payload')
        payload = data[offset + 8:offset + 8 + length]
        require(zlib.crc32(kind + payload) & 0xffffffff == struct.unpack('>I', data[offset + 8 + length:end])[0], 'PNG CRC mismatch')
        require(kind in (b'IHDR', b'IDAT', b'IEND', b'pHYs'), 'Unexpected PNG chunk')
        if kind == b'IHDR':
            require(not chunks and length == 13, 'Invalid PNG IHDR')
            width, height, depth, color, compression, filtering, interlace = struct.unpack('>IIBBBBB', payload)
            require(0 < width <= 10000 and 0 < height <= 10000 and (depth, color, compression, filtering, interlace) == (8, 2, 0, 0, 0), 'Invalid PNG raster format')
        elif kind == b'pHYs':
            require(chunks == [b'IHDR'] and length == 9, 'Invalid PNG physical dimensions')
            x, y, unit = struct.unpack('>IIB', payload)
            require(x > 0 and y > 0 and unit in (0, 1), 'Invalid PNG pixel density')
        elif kind == b'IDAT':
            require(chunks and chunks[-1] in (b'IHDR', b'pHYs', b'IDAT'), 'Invalid PNG data order')
            compressed.append(payload)
        else:
            require(compressed and length == 0 and end == len(data), 'Invalid PNG IEND')
        chunks.append(kind)
        offset = end
    require(chunks and chunks[0] == b'IHDR' and chunks[-1] == b'IEND' and compressed, 'Incomplete PNG')
    expected = height * (1 + width * 3)
    decoder = zlib.decompressobj()
    pixels = decoder.decompress(b''.join(compressed), expected + 1)
    require(decoder.eof and not decoder.unused_data and not decoder.unconsumed_tail and len(pixels) == expected, 'PNG raster size or compression failure')
    require(all(pixels[row * (1 + width * 3)] <= 4 for row in range(height)), 'Invalid PNG row filter')
    return {'width': width, 'height': height}


def main():
    if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):
        raise ValueError('Use python3 -I -S -B without optimization')
    h = load_helper()
    h.canonical(Path(__file__).absolute())
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True)
    ap.add_argument('--pins-sha', required=True)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--bootstrap', action='store_true')
    group.add_argument('--dependency-lock-sha')
    ap.add_argument('--render-dpi', type=int, default=120)
    ap.add_argument('--require-packaged-match', action='store_true')
    a = ap.parse_args()
    h.require(72 <= a.render_dpi <= 200, 'Render DPI must be 72 through 200')
    before = h.snapshot()
    h.check_inputs()
    flat, pins = h.flatten(True, a.pins_sha)
    out = h.new_output(a.output_dir)

    def binaries():
        result = {}
        for name in ('pdftex', 'pdflatex', 'kpsewhich', 'pdftotext', 'pdftoppm', 'pdfinfo'):
            invoked = Path('/usr/bin') / name
            resolved = invoked.resolve(strict=True)
            result[name] = {'invoked': str(invoked), 'resolved': str(resolved), 'sha256': h.sha(h.read(resolved))}
        resolved = Path(sys.executable).resolve(strict=True)
        result['python'] = {'invoked': sys.executable, 'resolved': str(resolved), 'sha256': h.sha(h.read(resolved))}
        return result

    expected_binaries = binaries()
    lock = None
    if not a.bootstrap:
        raw = h.read(ROOT / 'tools/BUILD_DEPENDENCIES_LOCK.json')
        h.require(h.sha(raw) == h.digest(a.dependency_lock_sha), 'Dependency lock differs from external pin')
        lock = h.parse(raw)
        h.require(set(lock) == {'format', 'executables', 'system_inputs', 'scope'} and lock['format'] == 'Report66 build dependencies v1' and lock['scope'] == SCOPE, 'Invalid toolchain lock schema')
        h.require(lock['executables'] == expected_binaries, 'Executable preflight mismatch')
        for filename, row in lock['system_inputs'].items():
            p = Path(filename)
            h.require(p.is_absolute() and p == p.resolve(strict=True) and any(filename.startswith(prefix) for prefix in SYSTEM_ROOTS), 'Invalid locked system path')
            data = h.read(p)
            h.require({'bytes': len(data), 'sha256': h.sha(data)} == row, 'System-input preflight mismatch: ' + filename)
    out.mkdir(mode=0o700)
    h.write_new(out / 'PRESERVATION_BEFORE.json', h.encoded(before))
    h.write_new(out / 'PREFLIGHT.json', h.encoded({'status': 'BOOTSTRAP' if a.bootstrap else 'PASS', 'dependency_lock_sha256': a.dependency_lock_sha, 'executable_preflight': expected_binaries, 'locked_system_inputs': len(lock['system_inputs']) if lock else None}))
    try:
        with tempfile.TemporaryDirectory(prefix='report66-typeset-', dir=out) as temp:
            work = Path(temp)
            cache, home = work / 'cache', work / 'home'
            cache.mkdir(); home.mkdir()
            h.write_new(work / 'Report66.tex', flat)
            env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'TZ': 'UTC', 'HOME': str(home),
                   'SOURCE_DATE_EPOCH': EPOCH, 'FORCE_SOURCE_DATE': '1', 'TEXMF': '{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
                   'TEXMFVAR': str(cache), 'TEXMFCONFIG': str(cache), 'TEXMFHOME': str(home), 'TEXFORMATS': str(cache),
                   'openin_any': 'p', 'openout_any': 'p', 'shell_escape': 'f', 'MKTEXPK': '0', 'MKTEXTFM': '0', 'MKTEXMF': '0'}
            system, recorder_receipts = {}, []

            def system_input(path):
                p = path.resolve(strict=True)
                h.require(any(str(p).startswith(prefix) for prefix in SYSTEM_ROOTS), 'Unexpected external TeX input: ' + str(p))
                data = h.read(p)
                row = {'bytes': len(data), 'sha256': h.sha(data)}
                h.require(str(p) not in system or system[str(p)] == row, 'System input changed between TeX passes')
                system[str(p)] = row
                if lock is not None:
                    h.require(lock['system_inputs'].get(str(p)) == row, 'Unpinned or changed executed TeX input: ' + str(p))
                return data

            def record(path, base, label):
                data = h.read(path)
                h.write_new(out / (label + '.fls'), data)
                inputs = set()
                for line in data.decode().splitlines():
                    if line.startswith('INPUT '):
                        p = Path(line[6:])
                        p = (p if p.is_absolute() else base / p).resolve(strict=True)
                        if p != work and work not in p.parents:
                            system_input(p); inputs.add(str(p))
                recorder_receipts.append({'pass': label, 'fls_sha256': h.sha(data), 'system_inputs': sorted(inputs)})

            def run(argv, cwd, label, timeout=240):
                name = Path(argv[0]).name
                h.require(name in expected_binaries and binaries() == expected_binaries, 'Executable changed before command')
                result = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
                h.write_new(out / (label + '.stdout'), result.stdout)
                h.require(result.returncode == 0, 'Command failed (' + label + '): ' + result.stdout.decode(errors='replace')[-5000:])
                return result.stdout

            run(['/usr/bin/pdftex', '-ini', '-etex', '-no-shell-escape', '-recorder', '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'], cache, 'format')
            record(cache / 'pdflatex.fls', cache, 'format')
            h.require((cache / 'pdflatex.fmt').is_file(), 'Fresh format missing')
            maps = []
            for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
                raw = run(['/usr/bin/kpsewhich', name], work, 'map-' + name, 30)
                lines = raw.decode().strip().splitlines()
                h.require(len(lines) == 1 and Path(lines[0]).is_absolute(), 'Ambiguous font-map path')
                maps.append(system_input(Path(lines[0])))
            h.write_new(cache / 'pdftex.map', b'\n'.join(maps) + b'\n')
            env['TEXFONTMAPS'] = str(cache) + ':'
            for number in range(1, 4):
                label = 'compile-' + str(number)
                final_stdout = run(['/usr/bin/pdflatex', '-no-shell-escape', '-recorder', '-halt-on-error', '-interaction=nonstopmode', '-file-line-error', 'Report66.tex'], work, label)
                # Capture before the next pass can overwrite the recorder.
                record(work / 'Report66.fls', work, label)
            warnings = (b'Overfull \\hbox', b'Overfull \\vbox', b'undefined references', b'undefined citations', b'Rerun to get cross-references right', b'Label(s) may have changed', b'rerunfilecheck Warning')
            h.require(not any(w in final_stdout for w in warnings), 'Final layout or reference warning')
            if lock is not None:
                h.require(system == lock['system_inputs'], 'All-pass executed TeX-input union differs from lock')
            for filename, row in system.items():
                data = h.read(Path(filename))
                h.require({'bytes': len(data), 'sha256': h.sha(data)} == row, 'System input changed during build')
            pdf = h.read(work / 'Report66.pdf')
            h.require(pdf.startswith(b'%PDF-'), 'Invalid PDF output')
            match = (ROOT / 'Report66.pdf').exists() and h.read(ROOT / 'Report66.pdf') == pdf
            h.require(not a.require_packaged_match or match, 'Packaged PDF differs')
            h.write_new(out / 'Report66.pdf', pdf)
            h.write_new(out / 'Report66.log', h.read(work / 'Report66.log'))
            run(['/usr/bin/pdftotext', '-layout', str(out / 'Report66.pdf'), str(out / 'Report66.txt')], work, 'pdftotext')
            info = run(['/usr/bin/pdfinfo', str(out / 'Report66.pdf')], work, 'pdfinfo')
            page_match = re.search(rb'^Pages:\s+([1-9][0-9]*)\s*$', info, re.M)
            h.require(page_match is not None, 'PDF page count missing')
            page_count = int(page_match.group(1))
            pages = out / 'pages'; pages.mkdir()
            run(['/usr/bin/pdftoppm', '-r', str(a.render_dpi), '-png', str(out / 'Report66.pdf'), str(pages / 'page')], work, 'render')
            rendered = sorted(pages.iterdir())
            names = [re.fullmatch(r'page-([0-9]+)\.png', p.name) for p in rendered]
            h.require(all(names) and sorted(int(m.group(1)) for m in names) == list(range(1, page_count + 1)), 'Rendered-page inventory differs from PDF count')
            raster_inventory = {}
            for p in rendered:
                data = h.read(p)
                raster_inventory[p.name] = {**validate_png(data, h.require), 'bytes': len(data), 'sha256': h.sha(data)}
            h.require(binaries() == expected_binaries, 'Executable post-build mismatch')
            dependencies = {'format': 'Report66 build dependencies v1', 'executables': expected_binaries, 'system_inputs': system, 'scope': SCOPE}
            if lock is not None:
                h.require(dependencies == lock, 'Post-build dependency receipt differs from preflight lock')
            h.write_new(out / 'BUILD_DEPENDENCIES.json', h.encoded(dependencies))
            h.write_new(out / 'RECORDER_INPUT_UNION.json', h.encoded({'passes': recorder_receipts, 'union': system, 'all_passes_retained': True}))
            h.write_new(out / 'PAGE_INVENTORY.json', h.encoded(raster_inventory))
            receipt = {'status': 'BOOTSTRAP' if a.bootstrap else 'PASS', 'pdf_sha256': h.sha(pdf), 'standalone_sha256': h.sha(flat),
                       'manuscript_pins_sha256': a.pins_sha, 'manuscript_pins': pins, 'source_date_epoch': int(EPOCH), 'render_dpi': a.render_dpi,
                       'page_count': page_count, 'all_png_crc_and_rasters_verified': True, 'fresh_format': True, 'recorded_passes': 4,
                       'recorder_union_complete': True, 'dependency_lock_verified': lock is not None, 'dependency_receipt_sha256': h.sha(h.encoded(dependencies)),
                       'shell_escape': False, 'packaged_pdf_match': match, 'release_preserved': True, 'scope': 'Typesetting and analytic illustration only; no scientific executable'}
        after = h.snapshot()
        h.require(before == after, 'Release changed during build')
        h.write_new(out / 'PRESERVATION_AFTER.json', h.encoded(after))
        h.write_new(out / 'BUILD_RECEIPT.json', h.encoded(receipt))
        print(h.encoded(receipt).decode())
    except BaseException as error:
        after = h.snapshot()
        h.write_new(out / 'PRESERVATION_AFTER_FAILURE.json', h.encoded(after))
        h.write_new(out / 'BUILD_FAILURE.json', h.encoded({'status': 'FAIL', 'error': str(error), 'release_preserved': before == after}))
        raise


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.SubprocessError, zlib.error) as error:
        print('BUILD REFUSED: ' + str(error), file=sys.stderr)
        raise SystemExit(2)
