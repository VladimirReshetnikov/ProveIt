"""Descriptor-pinned JSON I/O and atomic, no-clobber result publication.

The directory-descriptor pattern adapts the earlier Report152 companion. This
version writes and fsyncs a private temporary file, then publishes by exclusive
hard link, so a failed write never exposes a partial destination file.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import secrets
import stat

ROOT = Path(__file__).absolute().parent
RESULTS = ROOT / "results"
MAX_INPUT_BYTES = 1024 * 1024


class VerificationError(RuntimeError):
    """A mathematical check, input condition, or output policy failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def exact_equal(actual, expected, label):
    require(actual == expected, f"{label}: actual={actual!r}; expected={expected!r}")


def _absolute(path):
    raw = Path(path)
    require(".." not in raw.parts, "Parent traversal is refused")
    return Path(os.path.abspath(raw))


def _parent_fd(path):
    """Open every parent component with NOFOLLOW, retaining a pinned parent."""
    require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY"),
            "This companion requires POSIX O_NOFOLLOW and O_DIRECTORY")
    current = os.open(path.anchor, os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in path.parent.parts[1:]:
            following = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                dir_fd=current)
            os.close(current)
            current = following
        return current
    except BaseException:
        os.close(current)
        raise


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value):
    raise VerificationError(f"Nonfinite JSON constant is refused: {value}")


def load_json(source):
    """Read at most one MiB; reject symlinks, FIFOs and all nonregular inputs."""
    path = _absolute(source)
    directory = None
    fd = None
    try:
        directory = _parent_fd(path)
        fd = os.open(path.name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                     dir_fd=directory)
        info = os.fstat(fd)
        require(stat.S_ISREG(info.st_mode), "JSON input must be a regular file")
        require(info.st_size <= MAX_INPUT_BYTES, "JSON input exceeds one MiB")
        with os.fdopen(fd, "rb") as stream:
            fd = None
            data = stream.read(MAX_INPUT_BYTES + 1)
        require(len(data) <= MAX_INPUT_BYTES, "JSON input exceeds one MiB")
        return json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                          parse_constant=_reject_constant)
    except OSError as exc:
        raise VerificationError(f"JSON input cannot be opened safely: {exc}") from exc
    finally:
        if fd is not None:
            os.close(fd)
        if directory is not None:
            os.close(directory)


def encoded_json(data):
    return json.dumps(data, indent=2, sort_keys=True, allow_nan=False) + "\n"


def write_new_json(destination, data):
    """Atomically publish one unused .json filename strictly under results/.

    Parent directories must exist. No parent or final symlinks are followed.
    Exclusive hard-link publication refuses every pre-existing destination,
    including directories, FIFOs, regular files and dangling symlinks. All
    operations after traversal are relative to the pinned parent descriptor.
    """
    destination = _absolute(destination)
    try:
        relative = destination.relative_to(RESULTS)
    except ValueError as exc:
        raise VerificationError(f"Output must be strictly inside {RESULTS}") from exc
    require(bool(relative.parts) and relative.name.endswith(".json"),
            "Output must be a new .json file inside results/")
    payload = encoded_json(data).encode("utf-8")
    directory = _parent_fd(destination)
    temporary = None
    fd = None
    try:
        # Reject known collisions before performing even a temporary write.
        try:
            os.stat(destination.name, dir_fd=directory, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise FileExistsError(f"Output already exists: {destination}")
        temporary = ".report153-" + secrets.token_hex(16) + ".tmp"
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=directory)
        with os.fdopen(fd, "wb") as stream:
            fd = None
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, destination.name, src_dir_fd=directory,
                dst_dir_fd=directory, follow_symlinks=False)
        os.unlink(temporary, dir_fd=directory)
        temporary = None
        os.fsync(directory)
    finally:
        if fd is not None:
            os.close(fd)
        if temporary is not None:
            try:
                os.unlink(temporary, dir_fd=directory)
            except FileNotFoundError:
                pass
        os.close(directory)
