#!/usr/bin/env python3
"""Verify the delivered evidence in an isolated temporary copy.

The top-level integrity check runs before subprocesses. Child checkers may
write result JSON; the copy preserves all delivered records byte-for-byte.
"""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def check_manifest(root: Path) -> int:
    manifest = root / "SHA256SUMS"
    if not manifest.is_file():
        raise SystemExit("SHA256SUMS is missing; verify the complete delivered archive.")
    entries = 0
    for line in manifest.read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", 1)
        path = root / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root):
            raise SystemExit(f"Invalid or missing manifest entry: {relative}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Integrity check failed: {relative}")
        entries += 1
    return entries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also replay all direct whole-frame machine cases")
    args = parser.parse_args()
    if sys.flags.optimize:
        raise SystemExit("Assertions must be enabled. Run without Python -O.")
    root = Path(__file__).resolve().parent
    count = check_manifest(root)
    print(f"PASS: integrity of {count} files", flush=True)
    checks = [
        ("exact AX stack contracts", "logic", ["check_axiom_row_permutation.py"]),
        ("complete emitter and twelve role maps", "logic", ["check_full_row_emission.py"]),
        ("exact source candidate normal forms", "research/axiom_search", ["verify_candidates.py"]),
        ("fifteen helper source bisimulations", "research/axiom_search", ["check_macro_bridge.py"]),
        ("inherited-entry cost diagnostic", "research/axiom_search", ["price_modal.py"]),
        ("complete fast 246-state certificate", "composed246", ["code/verify_composed246.py"]),
    ]
    if args.full:
        checks.append(("direct whole-frame 246-state replay", "composed246", ["code/verify_whole_frame.py"]))
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="zfc-axiom-check-") as temp:
        work = Path(temp) / "packet"
        shutil.copytree(root, work)
        for label, directory, command in checks:
            tick = time.monotonic()
            run = subprocess.run([sys.executable, "-B", *command], cwd=work / directory,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if run.returncode:
                print(run.stdout)
                raise SystemExit(f"FAIL: {label} (exit {run.returncode})")
            print(f"PASS: {label} ({time.monotonic() - tick:.2f}s)", flush=True)
    print(f"PASS: {len(checks)} checks ({time.monotonic() - started:.2f}s); delivered files unchanged")


if __name__ == "__main__":
    main()
