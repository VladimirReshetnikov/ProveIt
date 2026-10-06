"""Descriptor-pinned, exclusive local I/O for the Report167 release."""
from contextlib import contextmanager
import os
from pathlib import Path
import stat


@contextmanager
def parent_handle(path):
    requested = Path(path)
    if '..' in requested.parts:
        raise ValueError('Parent traversal is not permitted')
    absolute = Path(os.path.abspath(requested))
    if absolute == Path('/'):
        raise ValueError('A named output is required')
    for flag in ('O_NOFOLLOW', 'O_DIRECTORY'):
        if not hasattr(os, flag):
            raise RuntimeError('POSIX ' + flag + ' is required')
    fd = os.open('/', os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in absolute.parts[1:-1]:
            next_fd = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = next_fd
        yield absolute, fd, absolute.name
    finally:
        os.close(fd)


@contextmanager
def fresh_file(path):
    with parent_handle(path) as (_, parent, leaf):
        fd = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=parent)
        with os.fdopen(fd, 'wb') as stream:
            yield stream


@contextmanager
def fresh_directory(path):
    with parent_handle(path) as (absolute, parent, leaf):
        os.mkdir(leaf, mode=0o700, dir_fd=parent)
        fd = os.open(leaf, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent)
        try:
            yield absolute, fd
        finally:
            os.close(fd)


def regular_bytes(path):
    with parent_handle(path) as (_, parent, leaf):
        fd = os.open(leaf, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW, dir_fd=parent)
        with os.fdopen(fd, 'rb') as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                raise ValueError('Input is not a regular file')
            return stream.read()


def write_member(directory_fd, name, content):
    if not name or name in ('.', '..') or '/' in name:
        raise ValueError('A single filename is required')
    fd = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                 0o600, dir_fd=directory_fd)
    with os.fdopen(fd, 'wb') as stream:
        stream.write(content)
