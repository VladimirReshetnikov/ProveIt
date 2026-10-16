#!/usr/bin/env python3
"""Check package integrity and replay the finite machine audit.

Python standard library only. This is not a Lean or Coq kernel check.
Use the documented compiler commands to reproduce those proof checks.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_relative(base: Path, rel: str) -> bytes:
    path = (base / rel).resolve()
    if not path.is_relative_to(base.resolve()) or not path.is_file():
        raise ValueError(f"Invalid manifest path: {rel}")
    return path.read_bytes()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for item in manifest["files"]:
        data = read_relative(ROOT, item["path"])
        require(len(data) == item["bytes"], f"Size mismatch: {item['path']}")
        require(digest(data) == item["sha256"], f"SHA-256 mismatch: {item['path']}")
    print(f"Package manifest: {len(manifest['files'])} files verified.", flush=True)

    coq = json.loads((ROOT / "internalization/upstream253_source_manifest.json").read_text())
    require(coq["modules"] == 160 and len(coq["files"]) == 160, "Coq closure count")
    total = 0
    for item in coq["files"]:
        data = read_relative(ROOT / "upstream253_sources", item["path"])
        total += len(data)
        require(len(data) == item["bytes"], f"Coq size: {item['path']}")
        require(digest(data) == item["sha256"], f"Coq hash: {item['path']}")
        git = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(git == item["git_blob_sha1"], f"Git blob: {item['path']}")
    require(total == coq["total_bytes"], "Coq closure byte count")
    print(f"Coq inspection closure: 160 exact Git blobs, {total} bytes.", flush=True)

    lean = json.loads((ROOT / "propositional_bridge/verification/verification.json").read_text())
    require(lean["source_modules"] == 10 and len(lean["modules"]) == 10, "Lean closure count")
    for item in lean["modules"]:
        data = read_relative(ROOT / "propositional_bridge", item["source"])
        require(digest(data) == item["source_sha256"], f"Lean source: {item['source']}")
        require(item["returncode"] == 0, f"Recorded Lean failure: {item['source']}")
    print("Lean evidence: all 10 source identities match the recorded successful build.", flush=True)
    print("No Lean or Coq kernel was invoked by these manifest checks.", flush=True)

    subprocess.run(
        [sys.executable, "-I", "-B", str(ROOT / "machine_audit/verify_audit.py")],
        check=True,
    )
    # The finite audit rewrites its deterministic summary; check it remained exact.
    for item in manifest["files"]:
        if item["path"] == "machine_audit/audit_summary.json":
            require(digest(read_relative(ROOT, item["path"])) == item["sha256"],
                    "Finite audit summary changed")
    print("PASS: package integrity, exact source identities, and finite machine audit.", flush=True)


if __name__ == "__main__":
    main()
