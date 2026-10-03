#!/usr/bin/env python3
"""Read-only package validation with fresh temporary exact-check replays."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
JOBS = [
    ("producer-bipartite", "reproducibility/producer/check_bipartite_orientation.py", "reproducibility/producer/verification.json", "verification.json"),
    ("producer-pendant", "reproducibility/producer/check_pendant_head_examples.py", "reproducibility/producer/pendant_verification.json", "pendant_verification.json"),
    ("independent-bipartite", "reproducibility/independent-bipartite/audit_bipartition.py", "reproducibility/independent-bipartite/verification.json", "verification.json"),
    ("independent-pendant", "reproducibility/independent-pendant/check_pendant_seed.py", "reproducibility/independent-pendant/verification.json", "verification.json"),
]


def canonical(value):
    if isinstance(value, dict):
        return {k:canonical(v) for k,v in value.items()
                if k not in {"seconds", "elapsed_seconds"}}
    if isinstance(value, list):
        return [canonical(v) for v in value]
    return value


def main():
    started = time.monotonic()
    manifest = ROOT / "SHA256SUMS"
    assert manifest.is_file(), "Missing release manifest"
    files = 0
    for line in manifest.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        path = ROOT / relative
        assert path.is_file(), f"Missing file: {relative}"
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        assert actual == digest, f"Hash mismatch: {relative}"
        files += 1
    print(f"PASS: {files} manifest hashes", flush=True)
    results = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    with tempfile.TemporaryDirectory(prefix="directed-support-replay-") as tmp:
        for name, script, expected, output in JOBS:
            directory = Path(tmp) / name
            directory.mkdir()
            copied = directory / Path(script).name
            shutil.copyfile(ROOT/script, copied)
            run = subprocess.run([sys.executable, str(copied)], cwd=directory,
                                 env=environment, text=True, capture_output=True)
            if run.returncode:
                print(run.stdout)
                print(run.stderr, file=sys.stderr)
                raise AssertionError(f"Checker failed: {name}")
            got = json.loads((directory/output).read_text())
            wanted = json.loads((ROOT/expected).read_text())
            assert canonical(got) == canonical(wanted), f"Receipt mismatch: {name}"
            results.append({"checker":name, "verdict":"PASS"})
            print(f"PASS: {name}; all deterministic receipt fields match", flush=True)
    print(json.dumps({"verdict":"PASS", "manifest_files":files,
                      "checks":results, "elapsed_seconds":round(time.monotonic()-started,3)}, indent=2))


if __name__ == "__main__":
    main()
