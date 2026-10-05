"""Explicit output guards for reader-package utilities; no assertion statements."""
import os
from pathlib import Path

def external_output(path, package_root):
    """Validate an absent external destination, rejecting symlink ancestors."""
    destination = Path(os.path.abspath(os.fspath(path)))
    package_root = Path(package_root).resolve()
    if destination == package_root or package_root in destination.parents:
        raise ValueError('OUTPUT_INSIDE_PACKAGE')
    for item in (destination, *destination.parents):
        if item.is_symlink():
            raise ValueError('OUTPUT_SYMLINK')
    if destination.exists():
        raise ValueError('OUTPUT_ALREADY_EXISTS')
    return destination

def write_external_bytes(path, data, package_root):
    destination = external_output(path, package_root)
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Check the directory chain again before the exclusive create.
    external_output(destination, package_root)
    with destination.open('xb') as stream:
        stream.write(data)
    return destination
