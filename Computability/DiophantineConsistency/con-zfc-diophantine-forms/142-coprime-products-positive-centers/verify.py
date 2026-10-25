#!/usr/bin/env python3
"""Run exact artifact checks; this does not decide Con(ZFC)."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integrity():
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        return {"distribution_manifest": "not yet written during assembly"}
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = ROOT / relative
        need(path.is_file(), "Missing distribution file: " + relative)
        need(digest(path) == expected, "Distribution digest differs: " + relative)
        count += 1
    return {"distribution_files_authenticated": count}


def cross_binding():
    review = json.loads((ROOT / "verification/product_review_checks.json").read_text())
    for filename, entry in review["graphs"].items():
        need(digest(ROOT / "products" / filename) == entry["sha256"],
             "Independent review graph differs: " + filename)
    binding = json.loads((ROOT / "products/parents/COEFFICIENT_BINDING.json").read_text())
    for name, entry in binding["ports"].items():
        a = gzip.decompress((ROOT / "products/coefficients" / entry["file"]).read_bytes())
        b = gzip.decompress((ROOT / "compact_xy/coefficients" / entry["file"]).read_bytes())
        need(a == b, "Compact components use different fixed port: " + name)
    return {"independent_review_graphs": len(review["graphs"]),
            "identical_compact_fixed_ports": len(binding["ports"])}


def run(relative, *arguments):
    script = ROOT / relative
    command = [sys.executable, "-B"]
    if sys.flags.optimize:
        command.append("-O")
    command += [str(script), *arguments]
    completed = subprocess.run(command, cwd=script.parent, capture_output=True,
                               text=True, check=True)
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError:
        result = completed.stdout.strip()
    return {"script": relative, "arguments": list(arguments),
            "exit_code": completed.returncode, "result": result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--integrity-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    result = {
        "scope": "Exact artifact checks; ordinary proofs and inherited calibration establish the unbounded theorem.",
        "python_optimization": sys.flags.optimize,
        "integrity": integrity(),
        "cross_binding": cross_binding(),
    }
    if not args.integrity_only:
        jobs = [
            ("products/build.py", "--check"),
            ("products/verify.py",),
            ("compact_xy/build.py", "--check"),
            ("compact_xy/verify.py",),
            ("compact_xy/rebuild_coefficients.py",),
            ("natural/verify.py", *(("--rebuild",) if args.rebuild else ())),
            ("natural/render.py", "--check"),
        ]
        result["checks"] = [run(*job) for job in jobs]
    result["passed"] = True
    payload = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload, end="")


if __name__ == "__main__":
    main()
