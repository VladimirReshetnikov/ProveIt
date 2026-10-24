#!/usr/bin/env python3
"""Temporarily restore35 pinned historical ZIPs around an argv command."""
from contextlib import contextmanager
import fcntl
from hashlib import sha1, sha256
import json
import os
from pathlib import Path
import signal
import stat
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[1]
METADATA = ROOT / 'research/historical-archives-compat/ARCHIVES.json'
METADATA_SHA256 = '4d27adacd05e23ec7881a1fc524399467b9bfde1216d9491e459a8db35ca2bb0'
COMMIT = 'e13c748234d6e7678fd35c934311a9227e90ef44'
SIGNALS = {signal.SIGINT, signal.SIGTERM, signal.SIGHUP}


class Interrupted(BaseException):
    def __init__(self, signum):
        self.signum = signum


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def read_regular(path):
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        require(stat.S_ISREG(info.st_mode), 'Not a regular file: ' + str(path))
        return info, stream.read()


def signal_child(child, signum):
    try:
        os.killpg(child.pid, signum)
    except ProcessLookupError:
        pass


@contextmanager
def defer_signals():
    previous = signal.pthread_sigmask(signal.SIG_BLOCK, SIGNALS)
    try:
        yield
    finally:
        signal.pthread_sigmask(signal.SIG_SETMASK, previous)


def verified_blobs():
    data = METADATA.read_bytes()
    require(sha256(data).hexdigest() == METADATA_SHA256, 'Historical archive metadata SHA256 mismatch')
    metadata = json.loads(data)
    records = metadata['archives']
    require(metadata['source_commit'] == COMMIT and metadata['archive_count'] == len(records) == 35,
            'Historical archive commit/count mismatch')
    require(git('rev-parse', COMMIT + '^{commit}').decode().strip() == COMMIT, 'Exact historical commit unavailable')
    tree = {}
    for entry in git('ls-tree', '-r', '-z', COMMIT, '--', 'docs/incoming').split(b'\0'):
        if entry:
            header, name = entry.split(b'\t', 1)
            mode, kind, oid = header.decode().split()
            tree[name.decode()] = (mode, kind, oid)
    seen = set()
    result = []
    for record in records:
        name = record['path']
        require(Path(name).parts[:2] == ('docs', 'incoming') and len(Path(name).parts) == 3
                and name.endswith('.zip') and name not in seen, 'Invalid or duplicate exact archive path')
        seen.add(name)
        require(record['commit'] == COMMIT and tree.get(name) ==
                (record['git_mode'], 'blob', record['git_blob']), 'Exact path/blob Git tree mismatch: ' + name)
        blob = git('cat-file', 'blob', record['git_blob'])
        require(len(blob) == record['bytes'] and sha256(blob).hexdigest() == record['sha256'],
                'Historical ZIP length/SHA256 mismatch: ' + name)
        require(sha1(b'blob ' + str(len(blob)).encode() + b'\0' + blob).hexdigest() == record['git_blob'],
                'Historical Git blob SHA1 mismatch: ' + name)
        result.append((REPO / name, record['sha256'], blob))
    return result


def run(command):
    require(command, 'Supply an argv command after --')
    require(Path(command[0]).name not in {'lean', 'lake'}, 'Lean remains paused; direct lean/lake commands are disabled')
    require(os.environ.get('CODEX_HISTORICAL_ARCHIVES_ACTIVE') != str(REPO), 'Nested archive wrappers would deadlock')
    git_dir = Path(git('rev-parse', '--absolute-git-dir').decode().strip())
    lock_fd = os.open(git_dir / 'historical-archives-compat.lock', os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600)
    created = []
    directories = []
    child = None
    cleanup_warnings = []
    previous_handlers = {}
    def interrupted(signum, _frame):
        raise Interrupted(signum)
    try:
        require(stat.S_ISREG(os.fstat(lock_fd).st_mode), 'Archive lock is not a regular file')
        for signum in SIGNALS:
            previous_handlers[signum] = signal.signal(signum, interrupted)
        fcntl.flock(lock_fd, fcntl.LOCK_EX)
        blobs = verified_blobs()
        for directory in [REPO / 'docs', REPO / 'docs/incoming']:
            if not os.path.lexists(directory):
                with defer_signals():
                    directory.mkdir()
                    info = directory.stat()
                    directories.append((directory, info.st_dev, info.st_ino))
            require(stat.S_ISDIR(directory.lstat().st_mode), 'Archive parent is missing, a symlink or not a directory')
        # Check every existing path before creating any historical path.
        missing = []
        for path, expected, blob in blobs:
            if os.path.lexists(path):
                _, current = read_regular(path)
                require(sha256(current).hexdigest() == expected, 'Existing archive differs; preserved without overwrite: ' + str(path))
            else:
                missing.append((path, expected, blob))
        for path, expected, blob in missing:
            # Hard-link a complete staged file with exclusive destination
            # creation; interruption before linking leaves no partial archive.
            with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.historical-archive-') as staged:
                staged.write(blob)
                staged.flush()
                with defer_signals():
                    os.link(staged.name, path, follow_symlinks=False)
                    info = path.lstat()
                    created.append((path, info.st_dev, info.st_ino, expected))
        env = dict(os.environ, CODEX_HISTORICAL_ARCHIVES_ACTIVE=str(REPO))
        child = subprocess.Popen(command, cwd=REPO, env=env, start_new_session=True)
        status = child.wait()
        return status if status >= 0 else 128 - status
    except Interrupted as exc:
        if child is not None and child.poll() is None:
            signal_child(child, exc.signum)
        return 128 + exc.signum
    finally:
        # Keep cleanup and unlocking atomic with respect to further handled
        # interrupts. Never remove a replaced or changed historical path.
        with defer_signals():
            if child is not None and child.poll() is None:
                signal_child(child, signal.SIGTERM)
                try:
                    child.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    signal_child(child, signal.SIGKILL)
                    child.wait()
            for path, device, inode, expected in reversed(created):
                try:
                    info, current = read_regular(path)
                    if (info.st_dev, info.st_ino) == (device, inode) and sha256(current).hexdigest() == expected:
                        again = path.lstat()
                        if (again.st_dev, again.st_ino) == (device, inode):
                            path.unlink()
                            continue
                    cleanup_warnings.append(str(path))
                except FileNotFoundError:
                    pass
                except (OSError, ValueError):
                    cleanup_warnings.append(str(path))
            for directory, device, inode in reversed(directories):
                try:
                    info = directory.lstat()
                    if stat.S_ISDIR(info.st_mode) and (info.st_dev, info.st_ino) == (device, inode):
                        directory.rmdir()
                except OSError:
                    pass
            for signum, handler in previous_handlers.items():
                signal.signal(signum, handler)
            os.close(lock_fd)
        for path in cleanup_warnings:
            print('Preserved changed/replaced historical archive: ' + path, file=sys.stderr)


def main():
    command = sys.argv[1:]
    if command == ['--help']:
        print(__doc__ + '\nUsage: with_historical_archives.py -- COMMAND [ARG ...]\nChild cwd is the repository; existing exact ZIPs are preserved.')
        return 0
    if command[:1] == ['--']:
        command = command[1:]
    try:
        return run(command)
    except FileNotFoundError as exc:
        print(str(exc), file=sys.stderr)
        return 127
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(str(exc), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
