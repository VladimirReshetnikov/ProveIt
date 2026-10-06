"""Descriptor-relative, exclusive file I/O that refuses every symlink component.

Linux/POSIX only. Existing parent directories are required. Paths containing '..'
are refused. O_NOFOLLOW plus directory descriptors avoids a check/use symlink race.
"""
from contextlib import contextmanager
import os
import stat
from exact import VerificationError


def _parts(path):
    value = os.fspath(path)
    if not isinstance(value, str) or not value or '\x00' in value:
        raise ValueError("expected a nonempty text pathname")
    if value.endswith(os.sep):
        raise ValueError("expected a file path, not a directory")
    if any(part == '..' for part in value.split(os.sep)):
        raise ValueError("parent traversal is forbidden")
    absolute = os.path.abspath(value)
    pieces = [part for part in absolute.split(os.sep) if part]
    if not pieces:
        raise ValueError("expected a file path")
    return pieces[:-1], pieces[-1]


@contextmanager
def _parent(path):
    if not hasattr(os, 'O_NOFOLLOW') or not hasattr(os, 'O_DIRECTORY'):
        raise RuntimeError("safe path operations require O_NOFOLLOW and O_DIRECTORY")
    directories, leaf = _parts(path)
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    current = os.open(os.sep, flags)
    try:
        for name in directories:
            next_fd = os.open(name, flags, dir_fd=current)
            os.close(current)
            current = next_fd
        yield current, leaf
    finally:
        os.close(current)


def write_fresh(path, payload):
    if type(payload) is not bytes:
        raise TypeError("payload must be bytes")
    with _parent(path) as (parent, leaf):
        fd = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=parent)
        try:
            view = memoryview(payload)
            while view:
                written = os.write(fd, view)
                if written <= 0:
                    raise OSError("short file write")
                view = view[written:]
            os.fsync(fd)
        finally:
            os.close(fd)


def read_regular(path, maximum_bytes=1_000_000):
    with _parent(path) as (parent, leaf):
        fd = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                     dir_fd=parent)
        try:
            mode = os.fstat(fd).st_mode
            if not stat.S_ISREG(mode):
                raise VerificationError("evidence must be a regular file")
            chunks, count = [], 0
            while True:
                chunk = os.read(fd, min(65536, maximum_bytes+1-count))
                if not chunk:
                    return b''.join(chunks)
                chunks.append(chunk)
                count += len(chunk)
                if count > maximum_bytes:
                    raise VerificationError("evidence file exceeds size limit")
        finally:
            os.close(fd)
