#!/usr/bin/env python3
"""Deterministic, no-clobber Report151 PDF and source ZIP builder.

Requires Python 3.10+, a POSIX filesystem with hard links and O_NOFOLLOW, and
TeX Live (pdftex/pdflatex plus the packages used by Report151.tex). No network.
Every final file is published atomically with an exclusive hard link; the two
files are not a single cross-file transaction. An existing output directory,
including an empty directory or dangling symlink, is always rejected.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import io
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import time
import zipfile

EPOCH = 1790985600
SOURCE_FILES = (
    "README.txt", "Report151.tex", "build.py", "companion.py",
    "foundation/Report149.pdf", "foundation/Report149.tex", "requirements.txt",
    "test_companion.py",
)
FOUNDATION_HASHES = {
    "foundation/Report149.tex": "0bb57104e7bd6efd1a11096c56222bd4a891f4bd1dc10cdb346988ce1c6ab24b",
    "foundation/Report149.pdf": "3b5edb943820dd6c061ccf0ad96a38cee0d3004550f75eef3a3eb70e865ea648",
}


def _absolute_parts(path):
    """Normalize relative paths without resolving away symlinks or '..'."""
    raw = os.fspath(path)
    if not raw or "\x00" in raw:
        raise ValueError("path must be nonempty and contain no NUL")
    if any(part == ".." for part in raw.split(os.sep)):
        raise ValueError("parent-traversal path components are rejected")
    if not os.path.isabs(raw):
        raw = os.path.join(os.getcwd(), raw)
    parts = tuple(part for part in raw.split(os.sep) if part not in ("", "."))
    return parts


@contextmanager
def secure_directory(path):
    """Open every path component without following symlinks; retain the fd."""
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY"):
        raise RuntimeError("this build requires POSIX O_NOFOLLOW and O_DIRECTORY")
    fd = os.open(os.sep, os.O_RDONLY | os.O_DIRECTORY)
    try:
        for part in _absolute_parts(path):
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        yield fd
    finally:
        os.close(fd)


def _relative_parts(name):
    if os.path.isabs(name):
        raise ValueError("source names must be relative")
    parts = name.split("/")
    if any(part in ("", ".", "..") for part in parts):
        raise ValueError("invalid relative source path")
    return parts


def read_regular(root_fd, name):
    """Read a regular source file, refusing symlinks in any relative component."""
    parts = _relative_parts(name)
    directory_fd = os.dup(root_fd)
    file_fd = None
    try:
        for part in parts[:-1]:
            child = os.open(part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory_fd)
            os.close(directory_fd)
            directory_fd = child
        # O_NONBLOCK prevents a substituted FIFO from blocking before fstat.
        file_fd = os.open(parts[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK,
                          dir_fd=directory_fd)
        before = os.fstat(file_fd)
        if not stat.S_ISREG(before.st_mode):
            raise ValueError(f"source is not a regular file: {name}")
        data = bytearray()
        while True:
            chunk = os.read(file_fd, 1024 * 1024)
            if not chunk:
                break
            data.extend(chunk)
        after = os.fstat(file_fd)
        if (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) != (
                after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns):
            raise RuntimeError(f"source changed while being read: {name}")
        if len(data) != before.st_size:
            raise RuntimeError(f"source changed size while being read: {name}")
        return bytes(data)
    finally:
        if file_fd is not None:
            os.close(file_fd)
        os.close(directory_fd)


def source_snapshot(source_dir):
    with secure_directory(source_dir) as fd:
        snapshot = {name: read_regular(fd, name) for name in SOURCE_FILES}
    for name, expected in FOUNDATION_HASHES.items():
        if hashlib.sha256(snapshot[name]).hexdigest() != expected:
            raise ValueError(f"unchanged foundation hash mismatch: {name}")
    tex = snapshot["Report151.tex"]
    for setting in (b"\\pdfinfoomitdate=1", b"\\pdftrailerid{}", b"\\pdfsuppressptexinfo="):
        if setting not in tex:
            raise ValueError(f"required deterministic PDF setting missing: {setting!r}")
    return snapshot


def deterministic_zip(files):
    stream = io.BytesIO()
    with zipfile.ZipFile(stream, "w", compression=zipfile.ZIP_STORED, allowZip64=True) as archive:
        for name in sorted(files):
            _relative_parts(name)
            info = zipfile.ZipInfo(name, time.gmtime(EPOCH)[:6])
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, files[name])
    return stream.getvalue()


def _run(command, cwd, env):
    result = subprocess.run(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, check=False)
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {' '.join(command)}\n"
                           + result.stdout[-20000:])


def compile_pdf(snapshot, work):
    """At least two passes, until stable, with a build-local format and maps."""
    work = Path(work)
    source = work / "source"
    source.mkdir()
    for name, data in snapshot.items():
        destination = source / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("xb") as handle:
            handle.write(data)
    env = {"PATH": os.defpath, "LC_ALL": "C", "LANG": "C",
                "SOURCE_DATE_EPOCH": str(EPOCH), "FORCE_SOURCE_DATE": "1", "TZ": "UTC",
                "TEXMF": "{/usr/share/texlive/texmf-dist,/usr/share/texmf}",
                "TEXFORMATS": str(work) + "//:", "TEXINPUTS": str(source) + "//:",
                "openout_any": "p", "shell_escape": "f"}
    for name in ("HOME", "TEXMFHOME", "TEXMFVAR", "TEXMFCONFIG", "TEXMFCACHE", "XDG_CACHE_HOME"):
        directory = work / name.lower()
        directory.mkdir()
        env[name] = str(directory)
    for program in ("pdftex", "pdflatex"):
        if shutil.which(program) is None:
            raise RuntimeError(f"required TeX Live command not found: {program}")
    _run(["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
          "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"], work, env)
    wrapper = ("\\pdfmapfile{}\\pdfmapfile{+cm.map}\\pdfmapfile{+cmextra.map}"
               "\\pdfmapfile{+symbols.map}\\pdfmapfile{+lm.map}\\pdfmapfile{+euler.map}"
               "\\input{Report151.tex}")
    previous = None
    for pass_number in range(1, 7):
        _run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
              "-file-line-error", "-jobname=Report151", wrapper], source, env)
        auxiliary = tuple((source / ("Report151." + suffix)).read_bytes()
                          if (source / ("Report151." + suffix)).exists() else b""
                          for suffix in ("aux", "out", "toc"))
        if pass_number >= 2 and auxiliary == previous:
            break
        previous = auxiliary
    else:
        raise RuntimeError("TeX auxiliary files did not stabilize within six passes")
    log = (source / "Report151.log").read_text(errors="replace")
    for warning in ("LaTeX Warning:", "LaTeX Font Warning:", "Package rerunfilecheck Warning:",
                    "Overfull ", "Underfull ", "Missing character:"):
        if warning in log:
            raise RuntimeError(f"final TeX log contains {warning!r}; inspect the source")
    with secure_directory(source) as fd:
        return read_regular(fd, "Report151.pdf")


def publish_exclusive(directory_fd, name, data):
    """Publish one complete byte string atomically, failing if name exists."""
    if len(_relative_parts(name)) != 1:
        raise ValueError("output filename must be a single component")
    # The temporary inode is created exclusively in the same pinned directory.
    token = os.urandom(16).hex()
    temporary = ".partial-" + token
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                 0o600, dir_fd=directory_fd)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fchmod(handle.fileno(), 0o644)
            os.fsync(handle.fileno())
        os.link(temporary, name, src_dir_fd=directory_fd, dst_dir_fd=directory_fd,
                follow_symlinks=False)
        os.fsync(directory_fd)
    finally:
        os.unlink(temporary, dir_fd=directory_fd)


def build(source_dir, output_dir):
    parts = _absolute_parts(output_dir)
    if not parts:
        raise ValueError("output directory cannot be the filesystem root")
    parent = os.sep + os.sep.join(parts[:-1])
    leaf = parts[-1]
    with secure_directory(parent) as parent_fd:
        try:
            os.stat(leaf, dir_fd=parent_fd, follow_symlinks=False)
        except FileNotFoundError:
            pass
        else:
            raise FileExistsError("output directory already exists (symlinks are rejected)")
        snapshot = source_snapshot(source_dir)
        with tempfile.TemporaryDirectory(prefix="report151-build-") as work:
            pdf = compile_pdf(snapshot, work)
        archive = deterministic_zip({**snapshot, "Report151.pdf": pdf})
        # mkdir is exclusive; even a late competing output or symlink cannot be replaced.
        os.mkdir(leaf, 0o755, dir_fd=parent_fd)
        output_fd = os.open(leaf, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=parent_fd)
        try:
            publish_exclusive(output_fd, "Report151.pdf", pdf)
            publish_exclusive(output_fd, "Report151-source.zip", archive)
            os.fsync(output_fd)
        finally:
            os.close(output_fd)
        os.fsync(parent_fd)
    return {"Report151.pdf": hashlib.sha256(pdf).hexdigest(),
            "Report151-source.zip": hashlib.sha256(archive).hexdigest()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", default=os.path.dirname(os.path.abspath(__file__)))
    parser.add_argument("--output-dir", required=True,
                        help="new directory under an existing, nonsymlink parent")
    args = parser.parse_args(argv)
    try:
        hashes = build(args.source_dir, args.output_dir)
    except (OSError, ValueError, RuntimeError) as exc:
        parser.exit(1, f"build refused or failed: {exc}\n")
    for name, digest in sorted(hashes.items()):
        print(f"{digest}  {os.path.join(args.output_dir, name)}")


if __name__ == "__main__":
    main()
