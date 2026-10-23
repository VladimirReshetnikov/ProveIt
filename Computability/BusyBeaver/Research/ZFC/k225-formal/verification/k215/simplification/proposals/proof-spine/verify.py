#!/usr/bin/env python3
"""Verify this research package without executing any repository source.

The sealed input tree is checked before and after execution. Selected newly
written static/finite checks run in a temporary copy. This is an integrity and
research-check harness, not a Lean or Rocq kernel or a security sandbox.
"""
import hashlib
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile

MANIFEST = "MANIFEST.sha256"
# Filled with the exact, newly authored checks selected for this release.
CHECKS = (
    ("review/verify_sources.py", ()),
    ("lean/audit_generic_spine.py", ()),
    ("rocq/check_oracle_cut.py", ()),
    ("rocq/test_oracle_cut.py", ()),
    ("audit/semantic_spine_audit.py", ()),
    ("audit/decrement_fork_replay.py", ()),
)


REPRODUCED_OUTPUTS = (
    "rocq/ORACLE_CUT_RESULT.json",
    "rocq/ORACLE_CUT_CONTROLS.json",
    "audit/decrement_fork_result.json",
)


def fail(message):
    raise RuntimeError(message)


def snapshot(root):
    result = {}
    for p in sorted(root.rglob("*")):
        if p.is_symlink():
            fail("Symlink not permitted in sealed package: " + str(p))
        if p.is_file():
            result[p.relative_to(root).as_posix()] = hashlib.sha256(p.read_bytes()).hexdigest()
        elif not p.is_dir():
            fail("Nonregular input: " + str(p))
    return result


def read_manifest(root):
    manifest_path = root / MANIFEST
    expected = {}
    for line_number, line in enumerate(manifest_path.read_text(encoding="utf-8").splitlines(), 1):
        if not line:
            continue
        pieces = line.split("  ", 1)
        if len(pieces) != 2:
            fail("Malformed manifest line " + str(line_number))
        digest, name = pieces
        path = PurePosixPath(name)
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            fail("Invalid digest on manifest line " + str(line_number))
        if path.is_absolute() or any(part in (".", "..") for part in path.parts) or str(path) != name:
            fail("Unsafe manifest path: " + name)
        if name == MANIFEST or name in expected:
            fail("Duplicate or self-referential manifest entry: " + name)
        expected[name] = digest
    if not expected:
        fail("Empty package manifest")
    return expected


def validate(root, before):
    expected = read_manifest(root)
    actual = {k: v for k, v in before.items() if k != MANIFEST}
    if set(actual) != set(expected):
        fail("Package file set differs from manifest. Missing: " + repr(sorted(set(expected) - set(actual))) +
             "; unexpected: " + repr(sorted(set(actual) - set(expected))))
    bad = sorted(name for name, digest in expected.items() if actual[name] != digest)
    if bad:
        fail("SHA-256 mismatch: " + repr(bad))
    return expected


def main():
    if not __debug__ or sys.flags.optimize:
        fail("Optimized Python is refused; rerun without -O or -OO")
    root = Path(__file__).resolve().parent
    before = snapshot(root)
    expected = validate(root, before)
    print("PASS: " + str(len(expected)) + " immutable manifest entries", flush=True)
    if not CHECKS:
        fail("Release has no selected checks")
    try:
        with tempfile.TemporaryDirectory(prefix="k215-proof-checks-") as tmp:
            work = Path(tmp) / "package"
            shutil.copytree(root, work)
            env = os.environ.copy()
            env.pop("PYTHONOPTIMIZE", None)
            env.pop("PYTHONPATH", None)
            env["PYTHONDONTWRITEBYTECODE"] = "1"
            for relative_script, arguments in CHECKS:
                if relative_script not in expected:
                    fail("Unmanifested checker: " + relative_script)
                script = work / relative_script
                command = [sys.executable, "-I", "-B", str(script), *arguments]
                print("RUN: " + relative_script, flush=True)
                result = subprocess.run(command, cwd=work, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                        timeout=600, check=False)
                print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
                if result.returncode != 0:
                    fail(relative_script + " exited " + str(result.returncode))
            for relative_output in REPRODUCED_OUTPUTS:
                actual = hashlib.sha256((work / relative_output).read_bytes()).hexdigest()
                if actual != expected[relative_output]:
                    fail("Reproduced output differs from archived result: " + relative_output)
            print("PASS: generated diagnostic outputs match archived bytes", flush=True)
    finally:
        after = snapshot(root)
        if after != before:
            fail("Input package changed during checks (including manifest bytes)")
    print("PASS: all selected new checks; input package unchanged", flush=True)
    print("NOT CHECKED: Lean/Rocq elaboration, kernel correctness, complete endpoint build", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)
