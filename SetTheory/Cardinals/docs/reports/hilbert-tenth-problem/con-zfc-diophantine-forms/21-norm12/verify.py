#!/usr/bin/env python3
"""Reproduce the finite checks for the Con(ZFC) norm12 package."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((ROOT / "SOURCE_MANIFEST.json").read_text())
    for row in manifest["upstream_files"]:
        path = ROOT / row["included_path"]
        if digest(path) != row["sha256"]:
            raise ValueError("Upstream source hash mismatch: " + str(path))

    expected = {
        "norm12_product.json":
          "ed0232c9530cebd14abfb079285eae16c2c603c624f0777aeb81447cba3d3021",
        "norm12_product_integer26.json":
          "1964e6c561674106683a21f24499d1b145b427972b2525af3d0ece76991d9016",
    }
    for name, sha in expected.items():
        if digest(ROOT / "arithmetic" / name) != sha:
            raise ValueError("Reviewed packet hash mismatch: " + name)

    checks = [
        "arithmetic/build_norm12.py",
        "arithmetic/build_norm12_lower_degree.py",
        "verification/audit_norm12.py",
        "coefficients/check_reduced.py",
    ]
    results = []
    for name in checks:
        started = time.monotonic()
        process = subprocess.run(
            [sys.executable, str(ROOT / name)],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False,
        )
        result = {
            "script": name, "exit_code": process.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
        }
        if process.returncode:
            result["stdout"] = process.stdout
            result["stderr"] = process.stderr
            results.append(result)
            raise RuntimeError(json.dumps(results, indent=2))
        result["status"] = "PASS"
        results.append(result)
        print(name + ": PASS", flush=True)
    for name, sha in expected.items():
        if digest(ROOT / "arithmetic" / name) != sha:
            raise ValueError("Emitter changed reviewed packet: " + name)

    windows = ROOT / "coefficients/reduced_t4_windows.json"
    binding = json.loads((ROOT / "COEFFICIENT_BINDING.json").read_text())
    assert digest(windows) == binding["alphabet_sha256"]
    receipt = {
        "status": "PASS",
        "repository_commit": manifest["commit"],
        "included_upstream_files_verified": len(manifest["upstream_files"]),
        "checks": results,
        "frozen_products_unchanged": True,
        "alphabet_sha256": digest(windows),
        "scope": (
            "Finite circuit identities, exact literal data and coefficient geometry. "
            "Not a proof-assistant build, coefficient digit expansion, K215 halting "
            "test, or proof of ZFC consistency."
        ),
    }
    (ROOT / "verification/REPRODUCTION.json").write_text(
        json.dumps(receipt, indent=2) + "\n"
    )
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
