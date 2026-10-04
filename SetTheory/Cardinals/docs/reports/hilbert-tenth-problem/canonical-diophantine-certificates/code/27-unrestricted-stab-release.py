#!/usr/bin/env python3
"""New Report54 release utility. Use python3 -I without -O.

Read-only verification, isolated deterministic PDF build, and deterministic ZIP
creation. The one-time author-only seal creates MANIFEST.json. No scientific
builder, original schedule, simulator, upstream executable, or Lean is run.
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

ROOT = Path(__file__).resolve().parent
EPOCH = '1791072000'
MANIFEST = 'MANIFEST.json'
SCHEMA = 'report54-release-manifest-v1'
PDF = 'article/Report54.pdf'
TEX = 'article/Report54.tex'

def require(value, message):
    if not value:
        raise RuntimeError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def emit(value):
    print(json.dumps(value, sort_keys=True, indent=2))

def inventory(root, timestamps=False):
    result = {}
    for path in [root] + sorted(root.rglob('*')):
        info = path.lstat()
        rel = '.' if path == root else path.relative_to(root).as_posix()
        require(stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode),
                'Nonregular or symlink entry: ' + rel)
        row = {'kind': 'file' if stat.S_ISREG(info.st_mode) else 'directory',
               'mode': stat.S_IMODE(info.st_mode)}
        if row['kind'] == 'file':
            row.update(bytes=info.st_size, sha256=digest(path.read_bytes()))
        if timestamps:
            row['mtime_ns'] = info.st_mtime_ns
        result[rel] = row
    return result

def output_path(raw, archive=False):
    absolute = raw.absolute()
    for part in [absolute] + list(absolute.parents):
        require(not part.is_symlink(), 'Symlink in output path')
    require(not os.path.lexists(absolute), 'Output must be fresh')
    require(absolute.parent.is_dir(), 'Output parent does not exist')
    path = absolute.resolve()
    require(path != ROOT and ROOT not in path.parents and path not in ROOT.parents,
            'Output must be outside and must not contain the release')
    if archive:
        require(path.suffix == '.zip', 'Archive output must end in .zip')
    return path

def verify(pin):
    path = ROOT / MANIFEST
    require(pin is not None and len(pin) == 64, 'Supply a trusted manifest SHA256')
    require(path.is_file() and not path.is_symlink(), 'Missing regular manifest')
    require(digest(path.read_bytes()) == pin, 'Manifest SHA256 mismatch')
    manifest = json.loads(path.read_text())
    require(manifest.get('schema') == SCHEMA, 'Manifest schema mismatch')
    actual = inventory(ROOT)
    require(actual[MANIFEST]['mode'] == 0o644, 'Unexpected manifest mode')
    del actual[MANIFEST]
    require(actual == manifest['entries'], 'Release inventory, bytes, or modes differ')
    return {'status': 'PASS', 'manifest_sha256': pin,
            'entries_verified': len(actual), 'exact_inventory': True}

def command(argv, cwd, env, log):
    with log.open('wb') as stream:
        result = subprocess.run(argv, cwd=cwd, env=env, stdout=stream,
                                stderr=subprocess.STDOUT, timeout=300)
    require(result.returncode == 0, 'Build command failed; see ' + str(log))

def build_pdf(args):
    out = output_path(args.output)
    before = inventory(ROOT, True)
    if not args.draft:
        verify(args.manifest_sha256)
    out.mkdir()
    shutil.copyfile(ROOT / TEX, out / 'Report54.tex')
    cache = out / 'tex-cache'
    cache.mkdir()
    env = dict(os.environ)
    env.update(TZ='UTC', SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE='1',
               TEXMFVAR=str(cache), TEXMFCONFIG=str(cache), TEXFORMATS=str(cache) + ':')
    def lookup(name):
        result = subprocess.run(['kpsewhich', name], cwd=out, env=env,
                                capture_output=True, text=True, timeout=30)
        return result.stdout.strip() if result.returncode == 0 else ''
    if not lookup('article.cls'):
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    if not lookup('pdflatex.fmt'):
        command(['pdftex', '-ini', '-etex', '-no-shell-escape',
                 '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex',
                 '-progname=pdflatex', 'pdflatex.ini'], cache, env, cache / 'format.log')
    if not lookup('pdftex.map'):
        pieces = []
        for name in ['lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']:
            path = lookup(name)
            require(bool(path), 'Missing installed font map: ' + name)
            pieces.append(Path(path).read_bytes())
        (cache / 'pdftex.map').write_bytes(b'\n'.join(pieces) + b'\n')
        env['TEXFONTMAPS'] = str(cache) + ':'
    for run in range(1, 4):
        command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', 'Report54.tex'], out, env, out / ('compile-%d.log' % run))
    pdf = out / 'Report54.pdf'
    require(pdf.is_file(), 'PDF was not generated')
    log = (out / 'compile-3.log').read_text()
    require('Overfull \\hbox' not in log and 'Overfull \\vbox' not in log,
            'Overfull layout box in final compile')
    require('undefined references' not in log and 'undefined citations' not in log,
            'Unresolved reference or citation')
    require(inventory(ROOT, True) == before, 'PDF build altered the release')
    same = (ROOT / PDF).is_file() and pdf.read_bytes() == (ROOT / PDF).read_bytes()
    if not args.draft:
        require(same, 'Rebuilt PDF differs from the packaged PDF')
    version = subprocess.run(['pdflatex', '--version'], capture_output=True,
                             text=True, timeout=30).stdout.splitlines()[0]
    receipt = {'status': 'PASS', 'pdf_sha256': digest(pdf.read_bytes()),
               'pdf_bytes': pdf.stat().st_size, 'packaged_pdf_identical': same,
               'release_preserved_bytes_modes_mtimes': True, 'shell_escape': False,
               'source_date_epoch': int(EPOCH), 'pdflatex': version,
               'no_overfull_boxes': True, 'references_resolved': True}
    (out / 'build-receipt.json').write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    emit(receipt)

def archive(args):
    out = output_path(args.output, True)
    before = inventory(ROOT, True)
    verify(args.manifest_sha256)
    entries = inventory(ROOT)
    with zipfile.ZipFile(out, 'x', compression=zipfile.ZIP_STORED, allowZip64=True) as bundle:
        for rel, row in sorted(entries.items()):
            if rel == '.':
                continue
            directory = row['kind'] == 'directory'
            entry = zipfile.ZipInfo(rel + '/' if directory else rel, (2026, 10, 4, 0, 0, 0))
            entry.create_system = 3
            entry.compress_type = zipfile.ZIP_STORED
            mode = row['mode'] | (stat.S_IFDIR if directory else stat.S_IFREG)
            entry.external_attr = (mode << 16) | (0x10 if directory else 0)
            bundle.writestr(entry, b'' if directory else (ROOT / rel).read_bytes())
    with zipfile.ZipFile(out) as bundle:
        require(bundle.testzip() is None, 'Archive CRC failure')
        for entry in bundle.infolist():
            if not entry.is_dir():
                require(bundle.read(entry.filename) == (ROOT / entry.filename).read_bytes(),
                        'Archive member content mismatch')
    require(inventory(ROOT, True) == before, 'Archive build altered the release')
    emit({'status': 'PASS', 'zip_sha256': digest(out.read_bytes()),
          'zip_bytes': out.stat().st_size, 'members': len(entries) - 1,
          'compression': 'ZIP_STORED', 'fixed_timestamp': '2026-10-04T00:00:00',
          'manifest_sha256': args.manifest_sha256,
          'release_preserved_bytes_modes_mtimes': True})

def seal():
    path = ROOT / MANIFEST
    require(not os.path.lexists(path), 'Manifest already exists; never overwrite a seal')
    data = {'schema': SCHEMA, 'date': '2026-10-04', 'entries': inventory(ROOT),
            'convention': 'Manifest excludes itself. Keep its trusted SHA256 outside the archive. Exact paths, bytes and POSIX modes are verified.'}
    path.write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')
    path.chmod(0o644)
    pin = digest(path.read_bytes())
    verify(pin)
    emit({'status': 'PASS', 'manifest_sha256': pin, 'entries': len(data['entries'])})

def main():
    require(sys.flags.isolated == 1 and sys.flags.optimize == 0,
            'Run this tool with python3 -I and without -O')
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
    main()
