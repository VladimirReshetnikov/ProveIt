#!/usr/bin/env python3
"""Offline, bounded, source-preserving Report277 build and deterministic package."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import signal
import stat
import subprocess
import time
import zipfile

ROOT = Path(__file__).absolute().parent
PDF_NAME = 'Report277.pdf'
ZIP_NAME = 'report277_all_degree_density.zip'
PIN_NAME = ZIP_NAME + '.sha256'
MANIFEST_NAME = 'MANIFEST.sha256'
ARCHIVE_ROOT = 'Report277/'
SOURCE_FILES = ('README.md', 'SOURCES.md', 'article.tex', 'build.py',
                'companion/exact_checks.py', 'tests/test_build.py', 'tests/test_companion.py')
PUBLIC_FILES = tuple(sorted((*SOURCE_FILES, PDF_NAME)))
FIXED_TIME = (2026, 10, 6, 0, 0, 0)
EPOCH = '1791244800'
MAX_FILE_BYTES = 12 * 1024 * 1024
MAX_SOURCE_BYTES = 32 * 1024 * 1024
MAX_ENTRIES = 64
MAX_LOG_BYTES = 4 * 1024 * 1024
MAX_TIMEOUT = 900


def _require_posix_handles():
    if (sys.platform != 'linux' or os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW')
            or not hasattr(os, 'O_DIRECTORY') or os.open not in os.supports_dir_fd
            or os.mkdir not in os.supports_dir_fd or not Path('/proc/self/fd').is_dir()):
        raise RuntimeError('Linux no-follow directory descriptors and /proc/self/fd required; no unsafe fallback')


def _open_directory(path, create=False):
    _require_posix_handles()
    if type(create) is not bool:
        raise ValueError('create must be a bool')
    raw = str(path)
    path = Path(path)
    if (not path.is_absolute() or raw.startswith('//') or '\x00' in raw
            or any(p in ('.', '..') for p in raw.split('/'))):
        raise ValueError('ordinary absolute directory required')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    descriptor = os.open('/', flags)
    try:
        for component in path.parts[1:]:
            try:
                child = os.open(component, flags, dir_fd=descriptor)
            except FileNotFoundError:
                if not create:
                    raise
                try:
                    os.mkdir(component, mode=0o700, dir_fd=descriptor)
                except FileExistsError:
                    pass
                child = os.open(component, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def _identity(info):
    return (info.st_dev, info.st_ino, info.st_mode, info.st_nlink, info.st_size,
            info.st_mtime_ns, info.st_ctime_ns)


def _read_regular(parent, name, limit=MAX_FILE_BYTES):
    before = os.stat(name, dir_fd=parent, follow_symlinks=False)
    if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1:
        raise RuntimeError('nonregular, symlink or hard-link source/output forbidden: ' + name)
    if before.st_size > limit:
        raise RuntimeError('file byte limit exceeded: ' + name)
    descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
    try:
        opened = os.fstat(descriptor)
        if _identity(opened) != _identity(before):
            raise RuntimeError('file changed before read: ' + name)
        chunks = []; total = 0
        while True:
            chunk = os.read(descriptor, min(65536, limit + 1 - total))
            if not chunk:
                break
            chunks.append(chunk); total += len(chunk)
            if total > limit:
                raise RuntimeError('file byte limit exceeded: ' + name)
        if (_identity(os.fstat(descriptor)) != _identity(opened)
                or _identity(os.stat(name, dir_fd=parent, follow_symlinks=False)) != _identity(opened)
                or total != opened.st_size):
            raise RuntimeError('file changed during read: ' + name)
        return b''.join(chunks)
    finally:
        os.close(descriptor)


def _directory_names(descriptor):
    names = []
    with os.scandir(descriptor) as iterator:
        for entry in iterator:
            names.append(entry.name)
            if len(names) > MAX_ENTRIES:
                raise RuntimeError('source entry limit exceeded')
    return sorted(names)


def snapshot():
    """Capture bounded bytes with no-follow handles; reject all file aliases."""
    files = {}; directories = set(); count = 0; total = 0
    def visit(parent, prefix=''):
        nonlocal count, total
        first_names = _directory_names(parent)
        for leaf in first_names:
            count += 1
            if count > MAX_ENTRIES:
                raise RuntimeError('source entry limit exceeded')
            name = prefix + leaf
            if (leaf in ('.', '..') or '\\' in leaf or '\x00' in leaf
                    or '\n' in leaf or '\r' in leaf):
                raise RuntimeError('invalid source name')
            info = os.stat(leaf, dir_fd=parent, follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                directories.add(name)
                child = os.open(leaf, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent)
                try:
                    held = os.fstat(child)
                    if (held.st_dev, held.st_ino) != (info.st_dev, info.st_ino):
                        raise RuntimeError('source directory changed before read')
                    visit(child, name + '/')
                    now = os.stat(leaf, dir_fd=parent, follow_symlinks=False)
                    if _identity(held) != _identity(now):
                        raise RuntimeError('source directory changed during read')
                finally:
                    os.close(child)
            elif stat.S_ISREG(info.st_mode):
                data = _read_regular(parent, leaf)
                total += len(data)
                if total > MAX_SOURCE_BYTES:
                    raise RuntimeError('source byte limit exceeded')
                files[name] = data
            else:
                raise RuntimeError('nonregular source entry or symlink forbidden: ' + name)
        if first_names != _directory_names(parent):
            raise RuntimeError('source directory listing changed during read')
    descriptor = _open_directory(ROOT)
    try:
        visit(descriptor)
    finally:
        os.close(descriptor)
    return files, directories


def inventory():
    files, directories = snapshot()
    return {name: hashlib.sha256(data).hexdigest() for name, data in files.items()}, directories


def _source_inventory(files):
    return ({n: hashlib.sha256(d).hexdigest() for n, d in files.items()},
            {p.as_posix() for n in files for p in Path(n).parents if p.as_posix() != '.'})


def manifest_bytes(files):
    return ''.join(hashlib.sha256(files[name]).hexdigest() + '  ' + name + '\n'
                   for name in sorted(files)).encode('ascii')


def _parse_manifest(data):
    if type(data) is not bytes or not data or len(data) > 128 * 1024:
        raise RuntimeError('missing or oversized manifest')
    try:
        text = data.decode('ascii')
    except UnicodeDecodeError as error:
        raise RuntimeError('malformed manifest encoding') from error
    expected = {}
    for line in text.splitlines():
        parts = line.split('  ', 1)
        if len(parts) != 2:
            raise RuntimeError('malformed manifest line')
        digest, name = parts
        if (not re.fullmatch('[0-9a-f]{64}', digest) or not name
                or name.startswith('/') or '\\' in name
                or any(p in ('', '.', '..') for p in name.split('/'))
                or name in expected or name == MANIFEST_NAME):
            raise RuntimeError('malformed manifest entry')
        expected[name] = digest
    if data != ''.join(d + '  ' + n + '\n' for n, d in sorted(expected.items())).encode('ascii'):
        raise RuntimeError('manifest must use canonical sorted LF entries')
    return expected


def verified_snapshot(require_manifest=False):
    if type(require_manifest) is not bool:
        raise ValueError('require_manifest must be a bool')
    files, directories = snapshot()
    wanted_dirs = {p.as_posix() for name in SOURCE_FILES for p in Path(name).parents
                   if p.as_posix() != '.'}
    if directories != wanted_dirs:
        raise RuntimeError('source directory inventory differs from exact allowlist')
    source_only = set(files) == set(SOURCE_FILES)
    distribution = set(files) == set(PUBLIC_FILES) | {MANIFEST_NAME}
    if not source_only and not distribution:
        raise RuntimeError('source inventory differs from exact allowlist')
    if require_manifest and not distribution:
        raise RuntimeError('manifest-pinned distribution required')
    if distribution:
        expected = _parse_manifest(files[MANIFEST_NAME])
        if set(expected) != set(PUBLIC_FILES):
            raise RuntimeError('manifest differs from exact public allowlist')
        actual = {n: hashlib.sha256(files[n]).hexdigest() for n in PUBLIC_FILES}
        if actual != expected:
            raise RuntimeError('source integrity mismatch')
    return files


def verify_manifest():
    files = verified_snapshot(require_manifest=True)
    return _parse_manifest(files[MANIFEST_NAME])


def external_location(value):
    if type(value) not in (str, type(Path())):
        raise ValueError('output must be an absolute path string or Path')
    raw = str(value)
    if (not raw or len(raw) > 4096 or '\x00' in raw or '\\' in raw or '~' in raw
            or raw.startswith('//') or not Path(raw).is_absolute()
            or any(p in ('.', '..') for p in raw.split('/'))):
        raise ValueError('ordinary absolute external output path required')
    path = Path(raw)
    dangerous = tuple(Path(p) for p in
        ('/bin', '/sbin', '/usr', '/etc', '/root', '/home', '/proc', '/sys', '/dev', '/run', '/var'))
    if (path in (Path('/'), Path('/tmp'), Path('/workspace'), Path('/workspace/shared'))
            or any(path == p or p in path.parents for p in dangerous)):
        raise ValueError('system/root output location forbidden')
    if path == ROOT or ROOT in path.parents or path in ROOT.parents:
        raise ValueError('output must be outside and not an ancestor of source')
    for ancestor in (path, *path.parents):
        if ancestor.is_symlink():
            raise ValueError('output symlink or symlink ancestor forbidden')
    return path


def output_directory(value, create=True):
    path = external_location(value)
    try:
        descriptor = _open_directory(path, create=create)
    except (NotADirectoryError, FileExistsError) as error:
        raise ValueError('output must be absent or an empty directory') from error
    try:
        if os.listdir(descriptor):
            raise ValueError('output must be absent or an empty directory')
    finally:
        os.close(descriptor)
    return path


def require_external_directory(value):
    return output_directory(value, create=False)


def _require_external_staging_directory(value):
    path = external_location(value)
    descriptor = _open_directory(path); os.close(descriptor)
    return path


@contextmanager
def _exclusive_stream(path):
    path = Path(path); parent = _open_directory(path.parent)
    try:
        descriptor = os.open(path.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o644, dir_fd=parent)
        with os.fdopen(descriptor, 'wb') as stream:
            yield stream
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                raise RuntimeError('output acquired a hard-link alias')
    finally:
        os.close(parent)


def _write_exclusive(path, data):
    if type(data) is not bytes:
        raise ValueError('output data must be bytes')
    with _exclusive_stream(path) as stream:
        stream.write(data)


def _output_bytes(path, limit=MAX_SOURCE_BYTES):
    path = Path(path); parent = _open_directory(path.parent)
    try:
        return _read_regular(parent, path.name, limit)
    finally:
        os.close(parent)


def _preflight(output, names):
    descriptor = _open_directory(output)
    try:
        for name in names:
            if type(name) is not str or '/' in name or name in ('', '.', '..'):
                raise ValueError('ordinary output basename required')
            try:
                os.stat(name, dir_fd=descriptor, follow_symlinks=False)
            except FileNotFoundError:
                continue
            raise ValueError('output already exists: ' + name)
    finally:
        os.close(descriptor)


def _mkdir(path):
    parent = _open_directory(Path(path).parent)
    try:
        os.mkdir(Path(path).name, mode=0o700, dir_fd=parent)
    finally:
        os.close(parent)


def environment():
    # Deliberate allowlist: do not inherit loader, Python, TeX, locale or PATH overrides.
    return dict(PATH='/usr/bin:/bin', HOME='/nonexistent',
        PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0', PYTHONINTMAXSTRDIGITS='640',
        SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')


def _bounded_integer(value, name, maximum):
    if type(value) is not int or not 1 <= value <= maximum:
        raise ValueError(name + ' must be an integer from 1 through ' + str(maximum))


def run(command, cwd, env, logfile, timeout=MAX_TIMEOUT, output_limit=MAX_LOG_BYTES):
    """Bound both pipes while running; return stdout, keep stderr in the log."""
    _bounded_integer(timeout, 'timeout', MAX_TIMEOUT)
    _bounded_integer(output_limit, 'output_limit', MAX_LOG_BYTES)
    if (type(command) not in (list, tuple) or not 1 <= len(command) <= 64
            or any(type(arg) is not str or not arg or len(arg) > 4096 or '\x00' in arg for arg in command)
            or not Path(command[0]).is_absolute()):
        raise ValueError('bounded argv with an absolute executable required')
    descriptor = _open_directory(cwd)
    proc = None; chunks = {'stdout': [], 'stderr': []}; count = 0
    try:
        with _exclusive_stream(logfile) as log:
            proc = subprocess.Popen(command, cwd='/proc/self/fd/' + str(descriptor),
                pass_fds=(descriptor,), env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                stdin=subprocess.DEVNULL, start_new_session=True)
            end = time.monotonic() + timeout
            with selectors.DefaultSelector() as selector:
                for label, stream in (('stdout', proc.stdout), ('stderr', proc.stderr)):
                    os.set_blocking(stream.fileno(), False)
                    selector.register(stream, selectors.EVENT_READ, label)
                while selector.get_map():
                    remaining = end - time.monotonic()
                    if remaining <= 0:
                        raise RuntimeError('subprocess timeout exceeded')
                    for key, _ in selector.select(min(remaining, 0.2)):
                        data = os.read(key.fd, 65536)
                        if not data:
                            selector.unregister(key.fileobj)
                            continue
                        count += len(data)
                        if count > output_limit:
                            raise RuntimeError('subprocess output limit exceeded')
                        chunks[key.data].append(data)
                remaining = end - time.monotonic()
                if remaining <= 0:
                    raise RuntimeError('subprocess timeout exceeded')
                try:
                    status = proc.wait(timeout=remaining)
                except subprocess.TimeoutExpired as error:
                    raise RuntimeError('subprocess timeout exceeded') from error
            stdout = b''.join(chunks['stdout']); stderr = b''.join(chunks['stderr'])
            log.write(b'--- stdout ---\n' + stdout + b'\n--- stderr ---\n' + stderr)
            if status:
                raise RuntimeError('command failed; inspect ' + Path(logfile).name)
            return stdout
    finally:
        if proc is not None:
            # Kill a leftover process group as well as the immediate child.
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=5)
            if proc.stdout is not None:
                proc.stdout.close()
            if proc.stderr is not None:
                proc.stderr.close()
        os.close(descriptor)


def compile_pdf(output):
    output = require_external_directory(output)
    source = verified_snapshot()
    before = _source_inventory(source)
    try:
        return _compile_pdf_stage(output, source)
    finally:
        if inventory() != before:
            raise RuntimeError('PDF compilation changed source inventory')


def _compile_pdf_stage(output, source):
    output = _require_external_staging_directory(output)
    _preflight(output, (PDF_NAME, 'tex-work', 'tex-format.log', 'tex-pass-1.log', 'tex-pass-2.log'))
    work = output / 'tex-work'; _mkdir(work)
    _write_exclusive(work / 'article.tex', source['article.tex'])
    env = environment()
    tex_roots = [str(p) for p in (Path('/usr/share/texlive/texmf-dist'),
        Path('/usr/share/texmf'), Path('/var/lib/texmf')) if p.is_dir()]
    if tex_roots:
        env['TEXMF'] = '{' + ','.join(tex_roots) + '}'
    env.update(openin_any='p', openout_any='p', shell_escape='f',
        MKTEXFMT='0', MKTEXPK='0', MKTEXTFM='0', TEXMFVAR='texmf-var', TEXMFCONFIG='texmf-config')
    run(['/usr/bin/pdftex', '-ini', '-no-shell-escape', '-etex', '-jobname=pdflatex',
         '-progname=pdflatex', '-interaction=nonstopmode', '-halt-on-error', 'pdflatex.ini'],
        work, env, output / 'tex-format.log')
    for number in range(1, 3):
        run(['/usr/bin/pdflatex', '-fmt=./pdflatex.fmt', '-no-shell-escape',
             '-interaction=nonstopmode', '-halt-on-error', 'article.tex'],
            work, env, output / ('tex-pass-' + str(number) + '.log'))
    log = _output_bytes(work / 'article.log').decode('utf-8', errors='replace')
    for defect in ('Overfull \\hbox', 'Overfull \\vbox', 'There were undefined references',
                   'There were multiply-defined labels', 'Rerun to get cross-references right',
                   'LaTeX Warning: Citation'):
        if defect in log:
            raise RuntimeError('TeX quality gate failed: ' + defect)
    pdf = _output_bytes(work / 'article.pdf', MAX_FILE_BYTES)
    if not pdf.startswith(b'%PDF-') or b'%%EOF' not in pdf[-1024:]:
        raise RuntimeError('compiler output is not a complete PDF')
    _write_exclusive(output / PDF_NAME, pdf)
    return hashlib.sha256(pdf).hexdigest()


def _package_zip_stage(output, members):
    output = _require_external_staging_directory(output)
    _preflight(output, (ZIP_NAME, PIN_NAME))
    names = sorted((*PUBLIC_FILES, MANIFEST_NAME))
    if set(members) != set(names):
        raise RuntimeError('ZIP input differs from exact public member allowlist')
    if members[MANIFEST_NAME] != manifest_bytes({n: members[n] for n in PUBLIC_FILES}):
        raise RuntimeError('ZIP input manifest mismatch')
    path = output / ZIP_NAME
    with _exclusive_stream(path) as stream:
        with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name in names:
                info = zipfile.ZipInfo(ARCHIVE_ROOT + name, FIXED_TIME)
                info.compress_type = zipfile.ZIP_DEFLATED; info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                archive.writestr(info, members[name], compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    data = _output_bytes(path)
    import io
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        infos = archive.infolist()
        if [i.filename for i in infos] != [ARCHIVE_ROOT + n for n in names] or archive.testzip() is not None:
            raise RuntimeError('ZIP inventory or CRC mismatch')
        for info, name in zip(infos, names):
            if (info.date_time != FIXED_TIME or info.create_system != 3
                    or info.external_attr != (stat.S_IFREG | 0o644) << 16
                    or info.compress_type != zipfile.ZIP_DEFLATED or info.flag_bits & 1
                    or info.extra or info.comment or archive.read(info) != members[name]):
                raise RuntimeError('ZIP metadata or member mismatch')
    digest = hashlib.sha256(data).hexdigest()
    _write_exclusive(output / PIN_NAME, (digest + '  ' + ZIP_NAME + '\n').encode('ascii'))
    return digest


def package_zip(output):
    output = require_external_directory(output)
    source = verified_snapshot(require_manifest=True); before = _source_inventory(source)
    try:
        return _package_zip_stage(output, source)
    finally:
        if inventory() != before:
            raise RuntimeError('packaging changed source inventory')


def _stage_sources(output, source):
    stage = output / 'check-work'; _mkdir(stage)
    for directory in ('companion', 'tests'):
        _mkdir(stage / directory)
    for name in SOURCE_FILES:
        _write_exclusive(stage / name, source[name])
    return stage


def reproduce(output):
    output = require_external_directory(output)
    source = verified_snapshot(); before = _source_inventory(source); env = environment()
    try:
        stage = _stage_sources(output, source)
        normal = {}
        for optimized, label in ((False, 'normal'), (True, 'optimized')):
            flags = ['-I', '-B', '-X', 'int_max_str_digits=640']
            if optimized:
                flags.append('-O')
            for name, script in (('builder-tests', 'tests/test_build.py'),
                                 ('companion-tests', 'tests/test_companion.py'),
                                 ('exact-checks', 'companion/exact_checks.py')):
                data = run([sys.executable, *flags, script], stage, env,
                           output / (name + '-' + label + '.log'))
                if optimized:
                    if data != normal[name]:
                        raise RuntimeError(name + ' stdout differs under optimization')
                else:
                    normal[name] = data
        if {n: _output_bytes(stage / n) for n in SOURCE_FILES} != {n: source[n] for n in SOURCE_FILES}:
            raise RuntimeError('checks changed staged source bytes')
        pdf_hash = _compile_pdf_stage(output, source)
        if MANIFEST_NAME in source and pdf_hash != hashlib.sha256(source[PDF_NAME]).hexdigest():
            raise RuntimeError('rebuilt PDF differs; inspect pinned TeX toolchain and logs')
        members = {n: source[n] for n in SOURCE_FILES}
        members[PDF_NAME] = _output_bytes(output / PDF_NAME, MAX_FILE_BYTES)
        members[MANIFEST_NAME] = manifest_bytes(members)
        _write_exclusive(output / MANIFEST_NAME, members[MANIFEST_NAME])
        zip_hash = _package_zip_stage(output, members)
        record = dict(status='passed', report=277, pdf_sha256=pdf_hash, zip_sha256=zip_hash,
            manifest_sha256=hashlib.sha256(members[MANIFEST_NAME]).hexdigest(),
            source_unchanged=inventory() == before, normal_and_optimized_checks='passed',
            matching_stdout=True, integer_digit_limit_in_subprocesses=640,
            python_version=sys.version.split()[0],
            scope='Bounded exact identities and regressions; written mathematics supplies the arbitrary-parameter proof')
        _write_exclusive(output / 'reproduction_receipt.json',
                         (json.dumps(record, indent=2, sort_keys=True) + '\n').encode('utf-8'))
        return record
    finally:
        if inventory() != before:
            raise RuntimeError('reproduction changed source inventory')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=('verify', 'reproduce', 'package'))
    parser.add_argument('--output', help='fresh absolute directory outside source')
    args = parser.parse_args(argv)
    try:
        source = verified_snapshot()
        if args.command == 'verify':
            if args.output is not None:
                raise ValueError('verify does not use an output directory')
            label = 'manifest-pinned distribution' if MANIFEST_NAME in source else 'seven-file source inventory'
            print('PASS: Report277 ' + label); return 0
        if args.output is None:
            raise ValueError('--output is required')
        output = output_directory(args.output)
        result = reproduce(output) if args.command == 'reproduce' else {'zip_sha256': package_zip(output)}
        print(json.dumps(result, indent=2, sort_keys=True)); return 0
    except (ValueError, RuntimeError, OSError, subprocess.TimeoutExpired, zipfile.BadZipFile) as error:
        parser.exit(1, 'ERROR: ' + str(error) + '\n')


if __name__ == '__main__':
    raise SystemExit(main())
