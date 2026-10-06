"""External, new-only output destinations; explicit guards survive python -O."""
import os
from pathlib import Path
import stat

class OutputError(ValueError):
    """A requested output could overwrite or escape its intended destination."""

def external_output(path, package_root):
    """Preflight without writing: a new path, real existing parent, no symlinks.

    Reject '..' rather than normalize through a possibly symlinked component.
    On POSIX, actual creation additionally walks parent directories with
    O_NOFOLLOW and opens the final file with O_EXCL. No parent is auto-created.
    """
    raw = os.fspath(path)
    if not raw or '\x00' in raw:
        raise OutputError('OUTPUT_INVALID_PATH')
    destination = Path(raw)
    if '..' in destination.parts:
        raise OutputError('OUTPUT_DOTDOT_COMPONENT')
    if not destination.is_absolute():
        destination = Path.cwd() / destination
    package_root = Path(package_root).resolve()
    if destination == package_root or package_root in destination.parents:
        raise OutputError('OUTPUT_INSIDE_BUNDLE')
    for component in reversed((destination, *destination.parents)):
        try:
            mode = component.lstat().st_mode
        except FileNotFoundError:
            if component != destination:
                raise OutputError('OUTPUT_PARENT_MISSING')
            continue
        if stat.S_ISLNK(mode):
            raise OutputError('OUTPUT_SYMLINK_COMPONENT')
        if component == destination:
            raise OutputError('OUTPUT_ALREADY_EXISTS')
        if not stat.S_ISDIR(mode):
            raise OutputError('OUTPUT_PARENT_NOT_DIRECTORY')
    # A resolved alias into the bundle must never become an output target.
    resolved = destination.resolve(strict=False)
    if resolved == package_root or package_root in resolved.parents:
        raise OutputError('OUTPUT_INSIDE_BUNDLE')
    return destination

def _open_parent(destination):
    """Open each real POSIX ancestor without following links."""
    if os.name != 'posix' or not hasattr(os, 'O_NOFOLLOW'):
        raise OutputError('OUTPUT_REQUIRES_POSIX_NOFOLLOW')
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    fd = os.open(destination.anchor, flags)
    try:
        for name in destination.parent.parts[1:]:
            next_fd = os.open(name, flags, dir_fd=fd)
            os.close(fd)
            fd = next_fd
        return fd
    except BaseException:
        os.close(fd)
        raise

def write_external_bytes(path, data, package_root):
    """Exclusively create an external regular file after a fresh preflight."""
    destination = external_output(path, package_root)
    parent_fd = _open_parent(destination)
    try:
        fd = os.open(destination.name, os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                     os.O_NOFOLLOW, 0o644, dir_fd=parent_fd)
        with os.fdopen(fd, 'wb') as stream:
            stream.write(data)
    finally:
        os.close(parent_fd)
    return destination

def create_external_directory(path, package_root):
    """Exclusively create one external directory; never overwrite or merge."""
    destination = external_output(path, package_root)
    parent_fd = _open_parent(destination)
    try:
        os.mkdir(destination.name, mode=0o700, dir_fd=parent_fd)
    finally:
        os.close(parent_fd)
    return destination
