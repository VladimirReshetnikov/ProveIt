#!/usr/bin/env python3
"""Small, standard-library package integrity helpers for Report174."""
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import zipfile

REPORT = "Report174"
MANIFEST = "manifest.json"
SOURCE_FILES = (
    "Report174.tex", "README.md", "build_package.py", "verify_package.py",
    "package_tools.py", "test_package_tools.py", "companion/exact_checks.py",
    "companion/symbolic_checks.py", "companion/run_checks.py",
)
GENERATED_FILES = ("Report174.pdf", "build_info.json", "verification.json")
PAYLOAD_FILES = tuple(sorted(SOURCE_FILES + GENERATED_FILES))
EPOCH = 1790985600  # 2026-10-03 00:00:00 UTC; overridden clock is reproducible.
ZIP_TIMESTAMP = (2026, 10, 3, 0, 0, 0)


class PackageError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise PackageError(message)


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True)+"\n").encode("utf-8")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def safe_regular_file(root, relative):
    root = Path(root)
    candidate = root / relative
    require(not root.is_symlink(), f"symlink root is not accepted: {root}")
    current = root
    for part in PurePosixPath(relative).parts:
        current = current / part
        require(not current.is_symlink(), f"symlink is not accepted: {current}")
    require(candidate.is_file(), f"missing regular file: {candidate}")
    require(stat.S_ISREG(candidate.stat().st_mode), f"not a regular file: {candidate}")
    return candidate


def inventory(root):
    root = Path(root)
    files = set()
    require(root.is_dir() and not root.is_symlink(), f"invalid package directory: {root}")
    for path in root.rglob("*"):
        require(not path.is_symlink(), f"symlink in package: {path}")
        if path.is_file():
            files.add(path.relative_to(root).as_posix())
        else:
            require(path.is_dir(), f"nonregular package member: {path}")
    return files


def make_manifest(root):
    root = Path(root)
    require(inventory(root) == set(PAYLOAD_FILES), "payload differs from explicit allowlist")
    return {"schema": "Report174.package.v1", "report": REPORT,
            "hash_algorithm": "sha256", "manifest_self_hash_excluded": True,
            "files": {name: {"sha256": digest(root/name), "bytes": (root/name).stat().st_size}
                      for name in PAYLOAD_FILES}}


def verify_directory(root):
    root = Path(root)
    raw = safe_regular_file(root, MANIFEST).read_bytes()
    try:
        manifest = json.loads(raw)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise PackageError(f"invalid manifest: {exc}") from exc
    require(manifest.get("schema") == "Report174.package.v1", "unknown manifest schema")
    require(manifest.get("hash_algorithm") == "sha256", "unexpected hash algorithm")
    expected = manifest.get("files", {})
    require(set(expected) == set(PAYLOAD_FILES), "manifest allowlist mismatch")
    require(inventory(root) == set(PAYLOAD_FILES) | {MANIFEST}, "unexpected or missing package members")
    for name in PAYLOAD_FILES:
        path = safe_regular_file(root, name)
        require(path.stat().st_size == expected[name].get("bytes"), f"size mismatch: {name}")
        require(digest(path) == expected[name].get("sha256"), f"SHA-256 mismatch: {name}")
    return manifest


def create_zip(root, output):
    root, output = Path(root), Path(output)
    verify_directory(root)
    with zipfile.ZipFile(output, "x", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name in sorted(set(PAYLOAD_FILES) | {MANIFEST}):
            info = zipfile.ZipInfo(REPORT+"/"+name, ZIP_TIMESTAMP)
            info.create_system = 3
            info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, (root/name).read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)


def extract_zip(archive_path, destination):
    """Strict extraction: exact names, bounded sizes, no duplicates or symlinks."""
    destination = Path(destination)
    require(not destination.exists(), "archive extraction destination already exists")
    allowed = {REPORT+"/"+name for name in set(PAYLOAD_FILES) | {MANIFEST}}
    with zipfile.ZipFile(archive_path) as archive:
        infos = archive.infolist()
        require(len(infos) == len(allowed) and {i.filename for i in infos} == allowed,
                "ZIP names differ from allowlist or contain duplicates")
        require(sum(i.file_size for i in infos) <= 100*1024*1024, "ZIP uncompressed size limit")
        for info in infos:
            require(not info.is_dir() and info.file_size <= 32*1024*1024, "ZIP member type/size limit")
            mode = info.external_attr >> 16
            require(not stat.S_ISLNK(mode), "ZIP symlink is not accepted")
            require(not info.flag_bits & 1, "encrypted ZIP is not accepted")
        destination.mkdir()
        for info in infos:
            relative = PurePosixPath(info.filename).relative_to(REPORT)
            path = destination.joinpath(*relative.parts)
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as stream:
                stream.write(archive.read(info))
    verify_directory(destination)
    return destination


def deterministic_environment():
    env = os.environ.copy()
    env.update({"SOURCE_DATE_EPOCH": str(EPOCH), "FORCE_SOURCE_DATE": "1",
                "TZ": "UTC", "LC_ALL": "C", "PYTHONHASHSEED": "0",
                "PYTHONDONTWRITEBYTECODE": "1"})
    return env
