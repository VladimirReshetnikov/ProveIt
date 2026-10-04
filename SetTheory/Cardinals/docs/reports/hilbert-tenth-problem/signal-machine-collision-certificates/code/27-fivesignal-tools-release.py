#!/usr/bin/env python3
"""Report57 release: exact verification, exclusive PDF builds, seal, stored ZIP.

Use python3 -I tools/release.py COMMAND. No scientific Python, saved program,
upstream executable, or physical simulation is executed by this utility.
The source tree must be quiescent while a command runs. This is a release
integrity tool, not an OS sandbox for hostile TeX or a concurrently hostile user.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import zipfile

ROOT = Path(__file__).absolute().parent.parent
MANIFEST = 'MANIFEST.json'
SCHEMA = 'report57-exact-release-v1'
EPOCH = 1791072000
ZIP_TIME = (2026, 10, 4, 0, 0, 0)
BUILD_INPUTS = ('Report57.tex', 'assets/guards.tex', 'assets/rules.tex')
SYSTEM_PREFIXES = ('/usr/share/', '/usr/lib/', '/usr/bin/', '/etc/texmf/', '/var/lib/texmf/')


class Failure(Exception):
    pass


def need(condition, message):
    if not condition:
        raise Failure(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + '\n').encode('ascii')


def emit(value):
    sys.stdout.buffer.write(encode(value))


def pin_valid(value):
    return type(value) is str and len(value) == 64 and all(c in '0123456789abcdef' for c in value)


def parse(data):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'Duplicate JSON key: ' + key)
            result[key] = value
        return result
    def invalid(value):
        raise Failure('Nonfinite JSON constant: ' + value)
    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid)


def checked_path(raw, fresh=False, regular=False):
    """Reject links, missing ancestors, special files and ambiguous traversal."""
    text = os.fspath(raw)
    path = Path(text)
    need(not text.startswith('//') and str(path) == text,
         'Use a canonical path without repeated separators or a trailing slash: ' + text)
    need(path.is_absolute() and not any(p in ('.', '..') for p in text.split('/')),
         'Use an absolute path without dot or parent traversal: ' + text)
    need(path != Path(path.anchor), 'Filesystem root cannot be a target')
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:], 1):
        current /= part
        leaf = index == len(path.parts) - 1
        try:
            info = current.lstat()
        except FileNotFoundError:
            need(leaf and fresh, 'Missing path or ancestor: ' + str(current))
            return path
        need(not stat.S_ISLNK(info.st_mode), 'Symlink path component: ' + str(current))
        need(not (leaf and fresh), 'Output already exists: ' + str(current))
        need(stat.S_ISREG(info.st_mode) if leaf and regular else stat.S_ISDIR(info.st_mode),
             'Unexpected path type: ' + str(current))
    return path


def external_output(raw, archive=False):
    path = checked_path(raw, fresh=True, regular=archive)
    need(path != ROOT and ROOT not in path.parents and path not in ROOT.parents,
         'Output must be outside and disjoint from the release tree')
    if archive:
        need(path.suffix == '.zip', 'Archive output needs a .zip suffix')
    return path


def read_file(path, allow_hardlinks=False):
    checked_path(path, regular=True)
    before = path.lstat()
    need(allow_hardlinks or before.st_nlink == 1, 'Hardlinked file is not allowed: ' + str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        start = os.fstat(fd)
        need((start.st_dev, start.st_ino) == (before.st_dev, before.st_ino), 'File changed at open')
        with os.fdopen(fd, 'rb', closefd=False) as stream:
            data = stream.read()
        end = os.fstat(fd)
        need((start.st_size, start.st_mtime_ns, start.st_ctime_ns) ==
             (end.st_size, end.st_mtime_ns, end.st_ctime_ns), 'File changed during read: ' + str(path))
        need(len(data) == end.st_size, 'Incomplete read: ' + str(path))
        return data
    finally:
        os.close(fd)


def write_new(path, data):
    checked_path(path, fresh=True, regular=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    try:
        with os.fdopen(fd, 'wb', closefd=False) as stream:
            stream.write(data)
            stream.flush()
            os.fsync(fd)
        os.fchmod(fd, 0o644)
    finally:
        os.close(fd)


def inventory(root=ROOT, preservation=False):
    checked_path(root)
    result = {}
    seen = set()
    def visit(path):
        info = path.lstat()
        isdir = stat.S_ISDIR(info.st_mode)
        need(isdir or stat.S_ISREG(info.st_mode), 'Symlink or special entry: ' + str(path))
        identity = (info.st_dev, info.st_ino)
        need(identity not in seen, 'Aliased file or directory: ' + str(path))
        seen.add(identity)
        rel = '.' if path == root else path.relative_to(root).as_posix()
        need(all(ord(c) >= 32 and c not in '\\\x7f' for c in rel), 'Unsafe member name: ' + repr(rel))
        row = {'kind': 'directory' if isdir else 'file', 'mode': stat.S_IMODE(info.st_mode)}
        if preservation:
            row.update(mtime_ns=info.st_mtime_ns, inode=info.st_ino, device=info.st_dev,
                       nlink=info.st_nlink)
        if isdir:
            result[rel] = row
            with os.scandir(path) as stream:
                children = sorted(entry.name for entry in stream)
            for name in children:
                visit(path / name)
        else:
            data = read_file(path)
            row.update(bytes=len(data), sha256=digest(data))
            result[rel] = row
    visit(root)
    return result


def verify(pin):
    need(pin_valid(pin), 'Supply the trusted, lowercase manifest SHA256')
    data = read_file(ROOT / MANIFEST)
    need(digest(data) == pin, 'Manifest SHA256 mismatch')
    obj = parse(data)
    need(type(obj) is dict and set(obj) == {'schema', 'source_date_epoch', 'entries'},
         'Manifest shape mismatch')
    need(obj['schema'] == SCHEMA and obj['source_date_epoch'] == EPOCH, 'Manifest format mismatch')
    actual = inventory()
    need(actual[MANIFEST]['mode'] == 0o644, 'Manifest mode must be 0644')
    del actual[MANIFEST]
    need(actual == obj['entries'], 'Release exact inventory, content, or mode mismatch')
    return {'status': 'PASS', 'manifest_sha256': pin, 'entries_verified': len(actual),
            'exact_inventory_bytes_modes': True}


def seal():
    checked_path(ROOT / MANIFEST, fresh=True, regular=True)
    entries = inventory()
    for rel, row in entries.items():
        need(row['mode'] == (0o755 if row['kind'] == 'directory' else 0o644),
             'Seal requires fixed 0755 directory / 0644 file modes: ' + rel)
    for name in (*BUILD_INPUTS, 'Report57.pdf'):
        need(name in entries and entries[name]['kind'] == 'file', 'Missing release artifact: ' + name)
    payload = encode({'schema': SCHEMA, 'source_date_epoch': EPOCH, 'entries': entries})
    write_new(ROOT / MANIFEST, payload)
    receipt = verify(digest(payload))
    receipt['schema'] = 'report57-seal-receipt-v1'
    emit(receipt)


def run(argv, cwd, env, log, timeout=300):
    checked_path(log, fresh=True, regular=True)
    with log.open('xb') as stream:
        proc = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                              stdout=stream, stderr=subprocess.STDOUT, timeout=timeout, check=False)
    need(proc.returncode == 0, 'TeX command failed; preserved diagnostic log: ' + str(log))


def system_file(path):
    resolved = path.resolve(strict=True)
    need(str(resolved).startswith(SYSTEM_PREFIXES), 'TeX dependency outside allowed system trees: ' + str(path))
    return resolved, read_file(resolved, allow_hardlinks=True)


def build_pdf(args):
    output = external_output(args.output)
    need(not args.draft or args.manifest_sha256 is None, '--draft cannot be combined with a manifest pin')
    need(bool(args.dependency_lock) == bool(args.dependency_lock_sha256),
         'Dependency lock needs both its path and trusted SHA256')
    expected_dependencies = None
    if args.dependency_lock:
        lock = checked_path(args.dependency_lock, regular=True)
        need(output not in lock.parents, 'Dependency lock cannot be inside the build output')
        data = read_file(lock)
        need(pin_valid(args.dependency_lock_sha256) and digest(data) == args.dependency_lock_sha256,
             'Dependency lock SHA256 mismatch')
        expected_dependencies = parse(data)
    before = inventory(preservation=True)
    if not args.draft:
        verify(args.manifest_sha256)
    source = {name: read_file(ROOT / name) for name in BUILD_INPUTS}
    output.mkdir(mode=0o700)
    try:
        (output / 'assets').mkdir(mode=0o700)
        for name, data in source.items():
            write_new(output / name, data)
        cache = output / 'tex-cache'
        home = output / 'home'
        cache.mkdir(mode=0o700)
        home.mkdir(mode=0o700)
        # Deliberately not os.environ.copy(): inherited TEXINPUTS, TEXMFHOME,
        # LD_PRELOAD, PYTHONPATH, BIBINPUTS and shell settings never propagate.
        env = {'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'TZ': 'UTC',
               'HOME': str(home), 'SOURCE_DATE_EPOCH': str(EPOCH), 'FORCE_SOURCE_DATE': '1',
               'TEXMF': '{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
               'TEXMFVAR': str(cache), 'TEXMFCONFIG': str(cache), 'TEXMFHOME': str(home),
               'TEXFORMATS': str(cache) + ':', 'openin_any': 'p', 'openout_any': 'p',
               'shell_escape': 'f', 'MKTEXPK': '0', 'MKTEXTFM': '0', 'MKTEXMF': '0'}
        def lookup(name):
            proc = subprocess.run(['/usr/bin/kpsewhich', name], cwd=output, env=env,
                                  stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=30)
            return proc.stdout.strip() if proc.returncode == 0 else ''
        # Build an isolated format every time; never consume a user format cache.
        run(['/usr/bin/pdftex', '-ini', '-etex', '-no-shell-escape', '-recorder',
             '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex',
             '-progname=pdflatex', 'pdflatex.ini'], cache, env, cache / 'format-compile.log')
        maps = []
        map_inputs = {}
        for name in ('lm.map', 'cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map'):
            found = lookup(name)
            need(bool(found), 'Missing installed TeX font map: ' + name)
            real, data = system_file(Path(found))
            map_inputs[str(real)] = {'bytes': len(data), 'sha256': digest(data)}
            maps.append(data)
        write_new(cache / 'pdftex.map', b'\n'.join(maps) + b'\n')
        env['TEXFONTMAPS'] = str(cache) + ':'
        # Omit path-/date-dependent PDF trailer metadata without changing source.
        tex = r'\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=-1\input{Report57.tex}'
        for number in range(1, 4):
            run(['/usr/bin/pdflatex', '-no-shell-escape', '-recorder', '-interaction=nonstopmode',
                 '-halt-on-error', '-jobname=Report57', tex], output, env,
                output / ('compile-%d.log' % number))
        log = read_file(output / 'compile-3.log').decode('utf-8', errors='replace')
        bad = ('Overfull \\hbox', 'Overfull \\vbox', 'undefined references',
               'undefined citations', 'Rerun to get cross-references right',
               'Label(s) may have changed', 'rerunfilecheck Warning')
        need(not any(word in log for word in bad), 'Layout/reference warning in final TeX pass')
        pdf = read_file(output / 'Report57.pdf')
        need(pdf.startswith(b'%PDF-'), 'Compiler did not produce a PDF')
        packaged = ROOT / 'Report57.pdf'
        same = os.path.lexists(packaged) and pdf == read_file(packaged)
        if not args.draft:
            need(same, 'Clean rebuilt PDF differs from the sealed PDF')
        system = dict(map_inputs)
        for recorder, cwd in ((cache / 'pdflatex.fls', cache), (output / 'Report57.fls', output)):
            for line in read_file(recorder).decode('utf-8').splitlines():
                if not line.startswith('INPUT '):
                    continue
                path = Path(line[6:])
                if not path.is_absolute():
                    path = cwd / path
                # Internal inputs are copied source or generated auxiliary data.
                path = Path(os.path.abspath(path))
                if path == output or output in path.parents:
                    continue
                real, data = system_file(path)
                system[str(real)] = {'bytes': len(data), 'sha256': digest(data)}
        executables = {}
        for name in ('pdflatex', 'pdftex', 'kpsewhich'):
            real, data = system_file(Path('/usr/bin') / name)
            executables[name] = {'resolved_path': str(real), 'bytes': len(data), 'sha256': digest(data)}
        dependencies = {'schema': 'report57-tex-dependencies-v1', 'system_inputs': system,
                        'executables': executables, 'source_date_epoch': EPOCH,
                        'scope': 'TeX recorder inputs and executable bytes; not dynamically linked system libraries'}
        if expected_dependencies is not None:
            need(dependencies == expected_dependencies, 'TeX dependency inventory or hash mismatch')
        dep_bytes = encode(dependencies)
        write_new(output / 'dependency-manifest.json', dep_bytes)
        receipt = {'schema': 'report57-pdf-build-v1', 'status': 'PASS', 'pdf_sha256': digest(pdf),
                   'pdf_bytes': len(pdf), 'packaged_pdf_identical': bool(same),
                   'dependency_manifest_sha256': digest(dep_bytes),
                   'dependency_lock_verified': expected_dependencies is not None,
                   'source_date_epoch': EPOCH, 'shell_escape': False, 'inherited_environment': False,
                   'no_overfull_boxes': True, 'references_resolved': True,
                   'source_inputs': {name: digest(data) for name, data in source.items()},
                   'release_preserved_bytes_modes_mtimes': True,
                   'scope': 'Three plain LaTeX inputs and installed TeX tools; no scientific code or simulation'}
    finally:
        need(inventory(preservation=True) == before, 'PDF build changed the release bytes, modes, mtimes or identity')
    write_new(output / 'build-receipt.json', encode(receipt))
    emit(receipt)


def archive(args):
    output = external_output(args.output, archive=True)
    before = inventory(preservation=True)
    verify(args.manifest_sha256)
    entries = inventory()
    # x mode preserves files, directories, links, and dangling links at the target.
    try:
        with zipfile.ZipFile(output, 'x', compression=zipfile.ZIP_STORED, allowZip64=True) as bundle:
            for rel, row in sorted(entries.items()):
                if rel == '.':
                    continue
                isdir = row['kind'] == 'directory'
                mode = 0o755 if isdir else 0o644
                need(row['mode'] == mode, 'Noncanonical ZIP mode: ' + rel)
                member = zipfile.ZipInfo(rel + '/' if isdir else rel, ZIP_TIME)
                member.create_system = 3
                member.compress_type = zipfile.ZIP_STORED
                member.external_attr = ((mode | (stat.S_IFDIR if isdir else stat.S_IFREG)) << 16) | (0x10 if isdir else 0)
                member.extra = b''
                member.comment = b''
                bundle.writestr(member, b'' if isdir else read_file(ROOT / rel))
        with zipfile.ZipFile(output) as bundle:
            expected = [rel + ('/' if row['kind'] == 'directory' else '')
                        for rel, row in sorted(entries.items()) if rel != '.']
            need(bundle.namelist() == expected and bundle.testzip() is None, 'ZIP member inventory/CRC mismatch')
            for member in bundle.infolist():
                rel = member.filename.rstrip('/')
                row = entries[rel]
                isdir = row['kind'] == 'directory'
                mode = (0o755 | stat.S_IFDIR) if isdir else (0o644 | stat.S_IFREG)
                need(member.date_time == ZIP_TIME and member.compress_type == zipfile.ZIP_STORED
                     and member.create_system == 3 and member.external_attr >> 16 == mode,
                     'ZIP fixed metadata mismatch: ' + rel)
                need(bundle.read(member) == (b'' if isdir else read_file(ROOT / rel)), 'ZIP byte mismatch: ' + rel)
    finally:
        need(inventory(preservation=True) == before, 'Archive changed release bytes, modes, mtimes or identity')
    data = read_file(output)
    emit({'schema': 'report57-zip-receipt-v1', 'status': 'PASS', 'zip_sha256': digest(data),
          'zip_bytes': len(data), 'members': len(entries) - 1, 'manifest_sha256': args.manifest_sha256,
          'compression': 'ZIP_STORED', 'timestamp': '2026-10-04T00:00:00',
          'fixed_modes': {'file': '0644', 'directory': '0755'},
          'release_preserved_bytes_modes_mtimes': True})


def main():
    need(sys.flags.isolated == 1 and sys.flags.optimize == 0, 'Run python3 -I, without -O')
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    check = sub.add_parser('verify')
    check.add_argument('--manifest-sha256', required=True)
    sub.add_parser('seal')
    build = sub.add_parser('build-pdf')
    build.add_argument('--output', required=True)
    build.add_argument('--draft', action='store_true')
    build.add_argument('--manifest-sha256')
    build.add_argument('--dependency-lock')
    build.add_argument('--dependency-lock-sha256')
    pack = sub.add_parser('archive')
    pack.add_argument('--output', required=True)
    pack.add_argument('--manifest-sha256', required=True)
    args = parser.parse_args()
    if args.command == 'verify':
        emit(verify(args.manifest_sha256))
    elif args.command == 'seal':
        seal()
    elif args.command == 'build-pdf':
        build_pdf(args)
    else:
        archive(args)


if __name__ == '__main__':
    try:
        main()
    except (Failure, OSError, ValueError, TypeError, KeyError, subprocess.SubprocessError) as error:
        print('RELEASE FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
