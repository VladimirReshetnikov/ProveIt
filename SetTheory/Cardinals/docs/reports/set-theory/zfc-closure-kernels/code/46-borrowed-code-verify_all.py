#!/usr/bin/env python3
"""Run the package's finite verifiers. No external checkout is required.

Passing these checks is not a proof of a Con(ZFC) equivalence. The report
identifies the ordinary theorems and the remaining formalization obligations.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def integrity(root):
    manifest = root / "SHA256SUMS"
    entries = manifest.read_text(encoding="utf-8").splitlines()
    seen = set()
    for line in entries:
        digest, relative = line.split("  ", 1)
        path = root / relative
        assert relative not in seen
        assert len(digest) == 64 and all(c in "0123456789abcdef" for c in digest)
        assert root in path.resolve().parents and path.is_file()
        assert hashlib.sha256(path.read_bytes()).hexdigest() == digest, relative
        seen.add(relative)
    assert seen, "Empty content manifest"
    return len(seen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path,
                        help="optional JSON result; choose a path outside the package")
    args = parser.parse_args()
    root = args.root.resolve()
    if args.output and (args.output.resolve() == root or root in args.output.resolve().parents):
        raise ValueError("Place verification output outside the immutable artifact package")
    checked = integrity(root)
    print(f"PASS integrity: {checked} files", flush=True)
    jobs = [
        ("initializer", "code/initializer/verify_initializers.py"),
        ("fusion", "code/fusion/verify.py"),
        ("independent_rows", "code/reviews/verify_initializer_rows.py"),
        ("support", "code/theory/support_diagnostic.py"),
    ]
    results = {}
    for name, relative in jobs:
        started = time.perf_counter()
        run = subprocess.run([sys.executable, "-B", str(root / relative)],
                             cwd=root, capture_output=True, text=True)
        if run.returncode:
            sys.stderr.write(run.stdout)
            sys.stderr.write(run.stderr)
            raise RuntimeError(f"Verifier failed: {relative}")
        result = json.loads(run.stdout)
        if name == "initializer":
            assert result["passed"] and result["controls_checked"] == 8
            detail = "8 full boots and exact state quotients"
        elif name == "fusion":
            assert result["verified"] and result["TM"]["working_states"] == 271
            detail = "4,549 relation pairs, 418 edges, exact 542-row regeneration"
        elif name == "independent_rows":
            assert result["row_equations_checked"] == 4912
            detail = "4,912 literal equations and analytical endpoints"
        else:
            assert result["status"] == "PASS" and result["decompositions"] == 226440
            detail = "226,440 factorizations, 2,880 tuple checks, 71 witnesses"
        seconds = time.perf_counter() - started
        print(f"PASS {name}: {detail} ({seconds:.2f}s)", flush=True)
        results[name] = {"seconds": seconds, "result": result}
    result = {"passed": True, "integrity_files": checked,
              "scope": "finite artifact checks; no new Con(ZFC) endpoint",
              "checks": results}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("All finite checks passed. Proof boundaries are documented in report.pdf.")


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled; Python -O is unsupported")
    main()
