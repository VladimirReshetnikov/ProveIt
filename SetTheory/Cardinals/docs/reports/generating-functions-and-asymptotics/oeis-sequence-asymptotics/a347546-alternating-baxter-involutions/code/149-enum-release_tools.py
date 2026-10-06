"""Small POSIX primitives used by the deterministic Report149 builders."""
from contextlib import contextmanager
import os
from pathlib import Path
import stat


def _components(path):
    supplied = Path(path)
    if '..' in supplied.parts:
        raise ValueError('Parent traversal is not permitted')
    absolute = Path(os.path.abspath(supplied))
    if absolute == Path('/'):
        raise ValueError('A named output is required')
    return absolute, absolute.parts[1:]


@contextmanager
def parent_handle(path):
    """Pin an existing parent, refusing every symlink component."""
    if not hasattr(os, 'O_NOFOLLOW') or not hasattr(os, 'O_DIRECTORY'):
        raise RuntimeError('POSIX O_NOFOLLOW and O_DIRECTORY are required')
    absolute, pieces = _components(path)
    handle = os.open('/', os.O_RDONLY | os.O_DIRECTORY)
    try:
        for component in pieces[:-1]:
            child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                            dir_fd=handle)
            os.close(handle)
            handle = child
        yield absolute, handle, pieces[-1]
    finally:
        os.close(handle)


@contextmanager
def fresh_file(path):
    with parent_handle(path) as (_, parent, leaf):
        handle = os.open(leaf, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=parent)
        with os.fdopen(handle, 'wb') as output:
            yield output


@contextmanager
def fresh_directory(path):
    with parent_handle(path) as (absolute, parent, leaf):
        os.mkdir(leaf, mode=0o700, dir_fd=parent)
        handle = os.open(leaf, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                         dir_fd=parent)
        try:
            yield absolute, handle
        finally:
            os.close(handle)


def regular_bytes(path):
    with parent_handle(path) as (_, parent, leaf):
        descriptor = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
        with os.fdopen(descriptor, 'rb') as source:
            if not stat.S_ISREG(os.fstat(source.fileno()).st_mode):
                raise ValueError('Input must be a regular file: ' + str(path))
            return source.read()


def write_member(directory_fd, name, content):
    if '/' in name or name in ('', '.', '..'):
        raise ValueError('A simple member name is required')
    descriptor = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                         0o600, dir_fd=directory_fd)
    with os.fdopen(descriptor, 'wb') as member:
        member.write(content)
