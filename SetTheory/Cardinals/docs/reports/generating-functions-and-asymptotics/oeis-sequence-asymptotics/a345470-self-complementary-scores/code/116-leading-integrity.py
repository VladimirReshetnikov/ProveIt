#!/usr/bin/env python3
"""Strict package integrity validation (integrity, not a publisher signature)."""
from hashlib import sha256
import json
from pathlib import Path, PurePosixPath
import re
import stat

class IntegrityError(RuntimeError):
    pass

def require(ok, code):
    if not ok:
        raise IntegrityError("INTEGRITY_FAILURE " + code)

def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "DUPLICATE_JSON_KEY")
        result[key] = value
    return result

def safe_path(value):
    if not isinstance(value, str) or not value:
        return False
    if re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_./-]*", value) is None:
        return False
    return (not value.startswith("/") and
            all(part not in {"", ".", ".."} for part in value.split("/")) and
            str(PurePosixPath(value)) == value and value != "manifest.json")

def read_manifest(path):
    try:
        data = json.loads(path.read_text(encoding="utf-8"),
                          object_pairs_hook=no_duplicate_keys)
    except IntegrityError:
        raise
    except (OSError, ValueError, UnicodeError) as exc:
        raise IntegrityError("INTEGRITY_FAILURE MANIFEST_PARSE") from exc
    require(isinstance(data, dict) and set(data) == {"format", "files"}, "MANIFEST_SCHEMA")
    require(data["format"] == "report116-sha256-v1", "MANIFEST_FORMAT")
    require(isinstance(data["files"], list) and len(data["files"]) > 0, "FILES_SCHEMA")
    paths = []
    for row in data["files"]:
        require(isinstance(row, dict) and set(row) == {"path", "bytes", "sha256"}, "ENTRY_SCHEMA")
        require(safe_path(row["path"]), "UNSAFE_PATH")
        require(type(row["bytes"]) is int and row["bytes"] >= 0, "SIZE_SCHEMA")
        require(isinstance(row["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) is not None, "HASH_SCHEMA")
        paths.append(row["path"])
    require(len(paths) == len(set(paths)), "DUPLICATE_PATH")
    require(paths == sorted(paths), "PATH_ORDER")
    return data

def validate(root):
    root = Path(root).resolve()
    manifest = root / "manifest.json"
    require(manifest.is_file() and not manifest.is_symlink(), "MANIFEST_TYPE")
    data = read_manifest(manifest)
    expected = {row["path"] for row in data["files"]} | {"manifest.json"}
    expected_dirs = set()
    for path in expected:
        parent = PurePosixPath(path).parent
        while str(parent) != ".":
            expected_dirs.add(str(parent))
            parent = parent.parent
    actual_files = set()
    actual_dirs = set()
    # lstat prevents a link from being accepted as a regular file or directory.
    for path in root.rglob("*"):
        relative = path.relative_to(root).as_posix()
        mode = path.lstat().st_mode
        require(not stat.S_ISLNK(mode), "SYMLINK")
        if stat.S_ISREG(mode):
            actual_files.add(relative)
        elif stat.S_ISDIR(mode):
            actual_dirs.add(relative)
        else:
            raise IntegrityError("INTEGRITY_FAILURE SPECIAL_FILE")
    require(actual_files == expected, "FILE_SET")
    require(actual_dirs == expected_dirs, "DIRECTORY_SET")
    for row in data["files"]:
        content = (root / row["path"]).read_bytes()
        require(len(content) == row["bytes"], "SIZE_MISMATCH " + row["path"])
        require(sha256(content).hexdigest() == row["sha256"], "HASH_MISMATCH " + row["path"])
    return {"status": "PASS", "format": data["format"], "files": len(data["files"])}

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        print(json.dumps(validate(args.root), sort_keys=True))
    except IntegrityError as exc:
        parser.exit(2, str(exc) + "\n")
