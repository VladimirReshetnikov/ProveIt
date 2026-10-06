"""Bounded JSON input and descriptor-pinned, atomic no-clobber output.

POSIX only. Every directory component is opened without following symlinks.
Publication uses an exclusive hard link to a completely written private file.
Importing this module performs no I/O and changes no interpreter settings.
"""
from __future__ import annotations

import json
import os
import secrets
import stat

MAX_INPUT_BYTES = 16384
MAX_OUTPUT_BYTES = 4 * 1024 * 1024


class InputError(ValueError):
    """An input, mathematical precondition, or safe-output policy failed."""


def require(condition, message):
    if not condition:
        raise InputError(message)


def _components(path):
    require(isinstance(path, (str, os.PathLike)), "Path must be text")
    raw = os.fspath(path)
    require(isinstance(raw, str) and raw and len(raw) <= 4096,
            "Path must be nonempty text of at most 4096 characters")
    require("\x00" not in raw and "\\" not in raw,
            "NUL and backslash are refused in paths")
    require(not raw.endswith("/"), "A file path cannot end with a slash")
    parts = raw.split("/")
    require(all(p not in (".", "..") for p in parts),
            "Dot and parent-traversal components are refused")
    require(all(parts[i] for i in range(1, len(parts))),
            "Empty path components are refused")
    # Capture an absolute lexical path before descriptor traversal. getcwd does
    # not resolve symlinks in the supplied path. Its physical cwd is the anchor
    # for a relative path, including when the shell's PWD uses a symlink.
    if not raw.startswith("/"):
        raw = os.getcwd().rstrip("/") + "/" + raw
    return raw.split("/")[1:]


def _parent_fd(path):
    require(os.name == "posix" and hasattr(os, "O_NOFOLLOW")
            and hasattr(os, "O_DIRECTORY"),
            "Safe I/O requires POSIX O_NOFOLLOW and O_DIRECTORY")
    parts = _components(path)
    require(bool(parts) and bool(parts[-1]), "Expected a file path")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    current = os.open("/", flags)
    try:
        for part in parts[:-1]:
            following = os.open(part, flags, dir_fd=current)
            os.close(current)
            current = following
        return current, parts[-1]
    except BaseException:
        os.close(current)
        raise


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON object key: " + key)
        result[key] = value
    return result


def _reject_number(value):
    raise InputError("Floating-point and nonfinite JSON numbers are refused")


def _bounded_integer(value):
    require(len(value) <= 12, "JSON integer token is too long")
    return int(value)


def _check_nesting(data):
    # Bound parser stack use before json.loads, ignoring brackets in strings.
    depth = 0
    quoted = escaped = False
    for byte in data:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            require(depth <= 16, "JSON nesting exceeds 16 levels")
        elif byte in (93, 125):
            depth -= 1


def read_json(path):
    directory = None
    descriptor = None
    try:
        directory, leaf = _parent_fd(path)
        descriptor = os.open(leaf, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                             dir_fd=directory)
        info = os.fstat(descriptor)
        require(stat.S_ISREG(info.st_mode), "Input must be a regular file")
        require(info.st_size <= MAX_INPUT_BYTES, "Input exceeds 16384 bytes")
        with os.fdopen(descriptor, "rb") as stream:
            descriptor = None
            data = stream.read(MAX_INPUT_BYTES + 1)
        require(len(data) <= MAX_INPUT_BYTES, "Input exceeds 16384 bytes")
        _check_nesting(data)
        return json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                          parse_int=_bounded_integer, parse_float=_reject_number,
                          parse_constant=_reject_number)
    except (OSError, UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise InputError("Cannot read valid safe JSON: " + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if directory is not None:
            os.close(directory)


def encoded_json(data):
    payload = (json.dumps(data, indent=2, sort_keys=True, allow_nan=False)
               + "\n").encode("utf-8")
    require(len(payload) <= MAX_OUTPUT_BYTES, "Output exceeds four MiB")
    return payload


def write_new_json(path, data):
    """Publish a fresh .json file. Existing paths are never replaced.

    Parent directories must exist. Readers see a complete file or no file.
    A failure after publication, such as a directory fsync error, may leave the
    complete output present; callers must not blindly retry or delete it.
    """
    payload = encoded_json(data)
    directory = None
    descriptor = None
    temporary = None
    try:
        directory, leaf = _parent_fd(path)
        require(leaf.endswith(".json"), "Output must have a .json suffix")
        try:
            os.stat(leaf, dir_fd=directory, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise InputError("Output already exists; choose a fresh filename")
        temporary = ".report155-" + secrets.token_hex(16) + ".tmp"
        descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL
                             | os.O_NOFOLLOW, 0o600, dir_fd=directory)
        with os.fdopen(descriptor, "wb") as stream:
            descriptor = None
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, leaf, src_dir_fd=directory, dst_dir_fd=directory,
                follow_symlinks=False)
        os.unlink(temporary, dir_fd=directory)
        temporary = None
        os.fsync(directory)
    except OSError as exc:
        raise InputError("Safe output failed: " + str(exc)) from exc
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if temporary is not None and directory is not None:
            try:
                os.unlink(temporary, dir_fd=directory)
            except FileNotFoundError:
                pass
        if directory is not None:
            os.close(directory)
