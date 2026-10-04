#!/usr/bin/env python3
"""Report56 release utility: isolated PDF build, exact seal, verify, stored ZIP.

Run with python3 -I, without -O. The PDF command executes installed TeX tools
with shell escape disabled; no scientific program, upstream code, or simulator
is executed. Paths must be absolute, fresh, nonsymlink, and disjoint outputs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import zipfile

ROOT = Path(__file__).absolute().parent
EPOCH = '1791072000'
MANIFEST = 'MANIFEST.json'
SCHEMA = 'report56-release-manifest-v1'
TEX = 'article/Report56.tex'
PDF = 'article/Report56.pdf'

class ReleaseError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise ReleaseError(message)

def walk_error(error):
    raise error

def sha(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('utf-8')

def emit(value):
    sys.stdout.buffer.write(encoded(value))

def strict_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result

def parse(data):
    def reject(value):
        raise ReleaseError('Invalid JSON constant: ' + value)
    return json.loads(data, object_pairs_hook=strict_object, parse_constant=reject)

def pin_ok(pin):
    return type(pin) is str and len(pin) == 64 and all(c in '0123456789abcdef' for c in pin)

def check_components(path, fresh=False, leaf_file=False):
    require(path.is_absolute() and '..' not in path.parts, 'Use an absolute path without parent traversal')
    require(path != Path(path.anchor), 'Filesystem root is not an input or output')
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:], 1):
        current /= part
        leaf = index == len(path.parts) - 1
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and fresh, 'Missing path or parent: ' + str(current))
            continue
        require(not stat.S_ISLNK(mode), 'Symlink path component: ' + str(current))
        if leaf and fresh:
            raise ReleaseError('Output must be fresh: ' + str(current))
        require(stat.S_ISREG(mode) if leaf and leaf_file else stat.S_ISDIR(mode),
                'Wrong file type: ' + str(current))
    return path

def output_path(raw, archive=False):
    path = check_components(raw, fresh=True, leaf_file=archive)
    require(path != ROOT and ROOT not in path.parents and path not in ROOT.parents,
            'Output must be disjoint from the release tree')
    if archive:
        require(path.suffix == '.zip', 'Archive output must end in .zip')
    return path

def read_regular(path):
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'Not a regular file: ' + str(path))
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0))
    try:
        opened = os.fstat(fd)
        require((opened.st_dev, opened.st_ino) == (before.st_dev, before.st_ino), 'File changed at open')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            data = stream.read()
        after = os.fstat(fd)
        require((after.st_size, after.st_mtime_ns) == (opened.st_size, opened.st_mtime_ns),
                'File changed while reading: ' + str(path))
    finally:
        os.close(fd)
    return data

def inventory(root, timestamps=False):
    check_components(root)
    result = {}
    for base, dirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        base = Path(base)
        for path in [base] + [base / name for name in sorted(files)]:
            info = path.lstat()
            require(stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode),
                    'Nonregular or symlink entry: ' + str(path))
            rel = '.' if path == root else path.relative_to(root).as_posix()
            row = {'kind': 'file' if stat.S_ISREG(info.st_mode) else 'directory',
                   'mode': stat.S_IMODE(info.st_mode)}
            if row['kind'] == 'file':
                data = read_regular(path)
                row.update(bytes=len(data), sha256=sha(data))
            if timestamps:
                row['mtime_ns'] = info.st_mtime_ns
            result[rel] = row
        for name in dirs:
            require(stat.S_ISDIR((base / name).lstat().st_mode),
                    'Non-directory or symlink entry: ' + str(base / name))
    return result

def write_new(path, data, mode=0o644):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, 'O_NOFOLLOW', 0), mode)
    try:
        with os.fdopen(fd, 'wb', closefd=False) as stream:
            stream.write(data)
            stream.flush()
        os.fchmod(fd, mode)
    finally:
        os.close(fd)

def verify(pin):
    require(pin_ok(pin), 'Supply a trusted lowercase manifest SHA256')
    check_components(ROOT)
    data = read_regular(ROOT / MANIFEST)
    require(sha(data) == pin, 'Manifest SHA256 mismatch')
    manifest = parse(data)
    require(type(manifest) is dict and manifest.get('schema') == SCHEMA, 'Manifest schema mismatch')
    actual = inventory(ROOT)
    require(actual[MANIFEST]['mode'] == 0o644, 'Unexpected manifest mode')
    del actual[MANIFEST]
    require(actual == manifest.get('entries'), 'Release exact inventory, bytes, or modes differ')
    return {'status': 'PASS', 'manifest_sha256': pin,
            'entries_verified': len(actual), 'exact_inventory_and_modes': True}

def command(argv, cwd, env, log, timeout=300):
    with log.open('xb') as stream:
        result = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                                stdout=stream, stderr=subprocess.STDOUT, timeout=timeout, check=False)
    require(result.returncode == 0, 'Build command failed; see ' + str(log))

def build_pdf(args):
    output = output_path(args.output)
    before = inventory(ROOT, True)
    if not args.draft:
        verify(args.manifest_sha256)
    else:
        require(args.manifest_sha256 is None, 'Do not combine --draft and a seal pin')
    source = read_regular(ROOT / TEX)
    output.mkdir(mode=0o700)
    try:
        write_new(output / 'Report56.tex', source)
        cache = output / 'tex-cache'
        cache.mkdir(mode=0o700)
        home = output / 'home'
        home.mkdir(mode=0o700)
        env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',
               'TZ': 'UTC', 'HOME': str(home), 'SOURCE_DATE_EPOCH': EPOCH, 'FORCE_SOURCE_DATE': '1',
               'TEXMFVAR': str(cache), 'TEXMFCONFIG': str(cache), 'TEXFORMATS': str(cache) + ':',
               'openin_any': 'p', 'openout_any': 'p', 'shell_escape': 'f'}
        def lookup(name):
            proc = subprocess.run(['kpsewhich', name], cwd=output, env=env,
                                  stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=30)
            return proc.stdout.strip() if proc.returncode == 0 else ''
        if not lookup('article.cls'):
            env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
        if not lookup('pdflatex.fmt'):
            command(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
                     '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                    cache, env, cache / 'format.log')
        if not lookup('pdftex.map'):
            pieces = []
            for name in ['lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']:
                path = lookup(name)
                require(bool(path), 'Missing installed font map: ' + name)
                pieces.append(read_regular(Path(path)))
            write_new(cache / 'pdftex.map', b'\n'.join(pieces) + b'\n')
            env['TEXFONTMAPS'] = str(cache) + ':'
        for run in range(1, 4):
            command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                     '-halt-on-error', 'Report56.tex'], output, env, output / ('compile-%d.log' % run))
        pdf = read_regular(output / 'Report56.pdf')
        log = (output / 'compile-3.log').read_text()
        require('Overfull \\hbox' not in log and 'Overfull \\vbox' not in log,
                'Overfull layout box in final compile')
        require('undefined references' not in log and 'undefined citations' not in log
                and 'Rerun to get cross-references right' not in log,
                'Unresolved reference or citation')
        packaged = ROOT / PDF
        same = packaged.is_file() and not packaged.is_symlink() and pdf == read_regular(packaged)
        if not args.draft:
            require(same, 'Rebuilt PDF differs from the packaged PDF')
        proc = subprocess.run(['pdflatex', '--version'], cwd=output, env=env,
                              stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=30, check=True)
        receipt = {'schema': 'report56-pdf-build-v1', 'status': 'PASS', 'pdf_sha256': sha(pdf),
                   'pdf_bytes': len(pdf), 'packaged_pdf_identical': same,
                   'release_preserved_bytes_modes_mtimes': True, 'shell_escape': False,
                   'source_date_epoch': int(EPOCH), 'pdflatex': proc.stdout.splitlines()[0],
                   'no_overfull_boxes': True, 'references_resolved': True,
                   'scope': 'Only self-contained Report56.tex and installed TeX tools; no scientific code execution'}
    finally:
        require(inventory(ROOT, True) == before, 'PDF build altered the release bytes, modes, or mtimes')
    write_new(output / 'build-receipt.json', encoded(receipt))
    emit(receipt)

def archive(args):
    output = output_path(args.output, archive=True)
    before = inventory(ROOT, True)
    verify(args.manifest_sha256)
    entries = inventory(ROOT)
    try:
        with zipfile.ZipFile(output, 'x', compression=zipfile.ZIP_STORED, allowZip64=True) as bundle:
            for rel, row in sorted(entries.items()):
                if rel == '.':
                    continue
                directory = row['kind'] == 'directory'
                entry = zipfile.ZipInfo(rel + '/' if directory else rel, (2026, 10, 4, 0, 0, 0))
                entry.create_system = 3
                entry.compress_type = zipfile.ZIP_STORED
                mode = row['mode'] | (stat.S_IFDIR if directory else stat.S_IFREG)
                entry.external_attr = (mode << 16) | (0x10 if directory else 0)
                bundle.writestr(entry, b'' if directory else read_regular(ROOT / rel))
        with zipfile.ZipFile(output) as bundle:
            expected = [rel + ('/' if row['kind'] == 'directory' else '')
                        for rel, row in sorted(entries.items()) if rel != '.']
            require(bundle.namelist() == expected and bundle.testzip() is None, 'ZIP inventory or CRC failure')
            for entry in bundle.infolist():
                row = entries[entry.filename.rstrip('/')]
                mode = row['mode'] | (stat.S_IFDIR if entry.is_dir() else stat.S_IFREG)
                require(entry.compress_type == zipfile.ZIP_STORED and entry.date_time == (2026, 10, 4, 0, 0, 0)
                        and (entry.external_attr >> 16) == mode, 'ZIP metadata mismatch')
                require(bundle.read(entry.filename) == (b'' if entry.is_dir() else read_regular(ROOT / entry.filename)),
                        'ZIP member content mismatch')
    finally:
        require(inventory(ROOT, True) == before, 'Archive build altered the release bytes, modes, or mtimes')
    emit({'schema': 'report56-stored-zip-v1', 'status': 'PASS', 'zip_sha256': sha(read_regular(output)),
          'zip_bytes': output.stat().st_size, 'members': len(entries) - 1, 'compression': 'ZIP_STORED',
          'fixed_timestamp': '2026-10-04T00:00:00', 'manifest_sha256': args.manifest_sha256,
          'release_preserved_bytes_modes_mtimes': True})

def seal():
    require(not os.path.lexists(ROOT / MANIFEST), 'Manifest already exists; never overwrite a seal')
    data = {'schema': SCHEMA, 'date': '2026-10-04', 'entries': inventory(ROOT),
            'convention': 'Manifest excludes itself. Preserve the trusted manifest SHA256 separately. Exact file and directory inventory, bytes, and POSIX modes are pinned.'}
    write_new(ROOT / MANIFEST, encoded(data))
    pin = sha(read_regular(ROOT / MANIFEST))
    verify(pin)
    emit({'status': 'PASS', 'manifest_sha256': pin, 'entries': len(data['entries'])})

def main():
    require(sys.flags.isolated == 1 and sys.flags.optimize == 0,
            'Run with python3 -I and without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    check = sub.add_parser('verify')
    check.add_argument('--manifest-sha256', required=True)
    build = sub.add_parser('build-pdf')
    build.add_argument('--output', type=Path, required=True)
    build.add_argument('--manifest-sha256')
    build.add_argument('--draft', action='store_true', help='Author-time unsealed build only')
    pack = sub.add_parser('archive')
    pack.add_argument('--output', type=Path, required=True)
    pack.add_argument('--manifest-sha256', required=True)
    sub.add_parser('seal', help='Author-only first manifest creation')
    args = parser.parse_args()
    if args.command == 'verify':
        emit(verify(args.manifest_sha256))
    elif args.command == 'build-pdf':
        build_pdf(args)
    elif args.command == 'archive':
        archive(args)
    else:
        seal()

if __name__ == '__main__':
    try:
        main()
    except (ReleaseError, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print('RELEASE FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
