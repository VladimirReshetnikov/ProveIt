"""Small POSIX descriptor-pinned I/O helpers; no overwrites or symlink traversal."""
import os
from pathlib import Path
import stat


def _parent_descriptor(path):
    raw = os.fspath(path)
    if not os.path.isabs(raw):
        raw = os.path.join(os.getcwd(), raw)
    parts = raw.split('/')
    if any(part == '..' for part in parts):
        raise ValueError('Parent-directory components are not permitted')
    parts = [part for part in parts if part and part != '.']
    if not parts:
        raise ValueError('A file path is required')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    current = os.open('/', flags)
    try:
        for component in parts[:-1]:
            following = os.open(component, flags, dir_fd=current)
            os.close(current)
            current = following
        return current, parts[-1]
    except BaseException:
        os.close(current)
        raise


def fresh_file(path, data):
    """Write bytes to a new regular file only; every parent must already exist."""
    parent, name = _parent_descriptor(path)
    descriptor = None
    created = False
    try:
        descriptor = os.open(name, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=parent)
        created = True
        with os.fdopen(descriptor, 'wb') as stream:
            descriptor = None
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        if descriptor is not None:
            os.close(descriptor)
        if created:
            os.unlink(name, dir_fd=parent)
        raise
    finally:
        os.close(parent)


def regular_bytes(path):
    """Read a regular file without following any final or parent symlink."""
    parent, name = _parent_descriptor(path)
    try:
        descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=parent)
        try:
            if not stat.S_ISREG(os.fstat(descriptor).st_mode):
                raise ValueError('Expected a regular file')
            with os.fdopen(descriptor, 'rb') as stream:
                descriptor = None
                return stream.read()
        finally:
            if descriptor is not None:
                os.close(descriptor)
    finally:
        os.close(parent)
