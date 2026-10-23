#!/usr/bin/env python3
"""Verify the sealed manuscript package without modifying its files.

Only the Python standard library is required. All checks remain active
under python -O. Success certifies the listed finite facts, not Con(ZFC).
"""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def run(script, *args):
    command = [sys.executable]
    if not __debug__:
        command.append("-O")
    command.extend([str(script), *map(str, args)])
    result = subprocess.run(command, capture_output=True, text=True, cwd=script.parent)
    require(result.returncode == 0,
            script.name + " failed:\n" + result.stdout + result.stderr)
    return result.stdout


def main():
    hashes = json.loads((ROOT / "RELEASE_HASHES.json").read_text())["files"]
    for name, expected in hashes.items():
        path = ROOT / name
        require(path.is_file(), "missing release file: " + name)
        require(sha256(path.read_bytes()) == expected, "changed release file: " + name)

    pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
    for entry in pins["included_evidence"]:
        raw = (ROOT / entry["local_file"]).read_bytes()
        require(git_blob(raw) == entry["expected_git_blob_sha1"],
                "source pin mismatch: " + entry["local_file"])
        require(sha256(raw) == entry["sha256"], "source SHA-256 mismatch")

    with tempfile.TemporaryDirectory(prefix="proveit_sparse_release_") as directory:
        copy = Path(directory) / "release"
        shutil.copytree(ROOT, copy, ignore=shutil.ignore_patterns(
            "__pycache__", "*.pyc", "*.aux", "*.log", "*.out"))
        construction = json.loads(run(copy / "construction" / "verify.py"))
        native = copy / "evidence" / "31-sun10" / "coefficients"
        native_receipt = json.loads(run(native / "build_coefficients.py"))
        for name in ("beta", "K", "MC", "MF_source"):
            rebuilt = (native / "payloads" / (name + ".bin.gz")).read_bytes()
            delivered = (ROOT / "construction" / "coefficients" / (name + ".bin.gz")).read_bytes()
            require(gzip.decompress(rebuilt) == gzip.decompress(delivered),
                    "native tuple reconstruction differs: " + name)
        minima = json.loads(run(copy / "minima" / "verify.py"))

    result = {
        "status": "PASS",
        "optimized_python": not __debug__,
        "scope": "Finite provenance, exact arithmetic, algebraic identities, degrees and reproduction; not a consistency decision or a new end-to-end formal proof",
        "release_files_hashed": len(hashes),
        "pinned_evidence_files": len(pins["included_evidence"]),
        "construction": construction,
        "native_tuple": {
            "instance": native_receipt["instance"],
            "raw_bytes": native_receipt["total_raw_bytes"],
            "gzip_bytes": native_receipt["total_gzip_bytes"],
            "exact_uncompressed_payload_match": True,
        },
        "minima": minima,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
