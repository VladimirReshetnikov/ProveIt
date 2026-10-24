#!/usr/bin/env python3
"""Authenticate the release; optionally replay its exact finite construction."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def release_files(root):
    return {
        p.relative_to(root).as_posix(): p
        for p in root.rglob("*")
        if p.is_file()
        and "__pycache__" not in p.parts
        and p.suffix != ".pyc"
        and p.relative_to(root).as_posix() != "MANIFEST.json"
    }


def authenticate():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    if manifest["algorithm"] != "sha256":
        raise ValueError("Unsupported manifest algorithm")
    wanted = manifest["files"]
    actual = release_files(ROOT)
    if set(actual) != set(wanted):
        raise ValueError("File set differs: " + repr({
            "missing": sorted(set(wanted) - set(actual)),
            "extra": sorted(set(actual) - set(wanted)),
        }))
    bad = [name for name, path in actual.items() if digest(path) != wanted[name]]
    if bad:
        raise ValueError("Changed release files: " + repr(bad))
    print(f"PASS: SHA-256 of all {len(wanted)} release files", flush=True)
    return manifest


def replay(manifest):
    steps = [
        ("integer-norms", "build.py", False),
        ("integer-norms", "check.py", False),
        ("integer-norms", "check.py", True),
        ("integer20", "build.py", False),
        ("integer20", "check.py", False),
        ("integer20", "check.py", True),
        ("direct-quartic", "replay.py", False),
    ]
    with tempfile.TemporaryDirectory(prefix="con-zfc-parity-replay-") as tmp:
        clone = Path(tmp) / "packet"
        shutil.copytree(ROOT, clone, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        for component, script, optimized in steps:
            command = [sys.executable] + (["-O"] if optimized else []) + [script]
            label = component + "/" + script + (" (-O)" if optimized else "")
            result = subprocess.run(command, cwd=clone / component, env=env,
                                    text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout, file=sys.stderr)
                raise RuntimeError("Failed: " + label)
            print("PASS: " + label, flush=True)
        changed = [
            name for name, sha in manifest["files"].items()
            if name.startswith(("integer-norms/", "integer20/", "direct-quartic/"))
            and digest(clone / name) != sha
        ]
        if changed:
            raise ValueError("Rebuilt artifacts differ from the release: " + repr(changed))
    print("PASS: regenerated artifacts match the release", flush=True)
    print("Scope: exact finite artifacts; unbounded mathematical proofs are in the report.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true",
                        help="rebuild and audit all components in a temporary copy")
    args = parser.parse_args()
    manifest = authenticate()
    if args.replay:
        replay(manifest)


if __name__ == "__main__":
    main()

