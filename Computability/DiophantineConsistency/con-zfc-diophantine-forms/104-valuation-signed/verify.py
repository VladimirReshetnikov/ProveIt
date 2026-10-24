#!/usr/bin/env python3
"""Reproduce the exact finite claims of this release (standard library only).

Ordinary unbounded proofs and imported calibrations are documented separately.
Run with -O to confirm no verification obligation depends on assert.
"""
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


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def run(script, args, cwd, receipts):
    command = [sys.executable]
    if sys.flags.optimize:
        command.append("-O")
    command += [str(script)] + [str(a) for a in args]
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    completed = subprocess.run(command, cwd=cwd, env=env, text=True,
                               capture_output=True)
    name = str(script.relative_to(ROOT)) if script.is_relative_to(ROOT) else script.name
    require(completed.returncode == 0,
            name + " failed:\n" + completed.stdout + "\n" + completed.stderr)
    receipts.append({"check": name, "status": "PASS"})
    print("PASS", name, flush=True)
    return completed.stdout


def check_manifest():
    manifest = read(ROOT / "MANIFEST.json")
    entries = manifest["files"]
    require(entries, "nonempty release manifest")
    for row in entries:
        relative = Path(row["path"])
        require(not relative.is_absolute() and ".." not in relative.parts,
                "safe manifest path")
        path = ROOT / relative
        require(path.is_file(), "missing release file: " + row["path"])
        raw = path.read_bytes()
        require(len(raw) == row["bytes"], "file size: " + row["path"])
        require(hashlib.sha256(raw).hexdigest() == row["sha256"],
                "file hash: " + row["path"])
    return len(entries)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt", type=Path)
    options = parser.parse_args()
    manifest_count = check_manifest()
    print("PASS release manifest", manifest_count, "files", flush=True)
    checks = []
    with tempfile.TemporaryDirectory(prefix="conzfc-release-") as directory:
        scratch = Path(directory)
        integer = ROOT / "integer12"
        generated = scratch / "equations"
        generated.mkdir()
        for variant, degree in [("rational", 2400), ("integral", 2912)]:
            name = "prime_separated12_degree" + str(degree) + ".json"
            run(integer / "build_prime12.py",
                ["--variant", variant, "--output", generated / name], ROOT, checks)
            require((generated / name).read_bytes() ==
                    (integer / "equations" / name).read_bytes(),
                    "exact regenerated circuit: " + name)
        prime_receipt = scratch / "prime12.json"
        run(integer / "check_prime12.py",
            ["--source-root", integer / "inherited/root_fusion",
             "--equations", generated, "--receipt", prime_receipt], ROOT, checks)
        norm_receipt = scratch / "norm.json"
        run(integer / "check_norm_exact.py", ["--receipt", norm_receipt], ROOT, checks)

        direct = ROOT / "direct"
        run(direct / "build.py", ["--check"], direct, checks)
        direct_receipt = scratch / "direct.json"
        run(direct / "verify.py",
            [direct, "--receipt", direct_receipt], direct, checks)
        run(direct / "verify_projection.py",
            [direct / "input/equation.json", direct / "output"], direct, checks)

        # These original supplemental programs write beside their source.
        # Run an exact temporary copy so retained source receipts stay unchanged.
        supplemental = scratch / "ordinary98"
        shutil.copytree(ROOT / "supplemental/ordinary98", supplemental,
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        run(supplemental / "build.py", [], supplemental, checks)
        for name in ["ordinary12_98.json", "ordinary12_parent100.json"]:
            require((supplemental / name).read_bytes() ==
                    (ROOT / "supplemental/ordinary98" / name).read_bytes(),
                    "exact supplemental regeneration: " + name)
        run(supplemental / "check.py", [], supplemental, checks)

        prime = read(prime_receipt)
        norm = read(norm_receipt)
        direct_summary = read(direct_receipt)
        supplemental_summary = read(supplemental / "CHECKS.json")
        require(norm["matched_terms"] == 20349, "full generic norm census")
        require(direct_summary["output_metrics"]["variables"] == 1190,
                "direct coordinate census")
        require(direct_summary["output_metrics"]["expanded_monomials"] == 26411,
                "direct term census")
        require(supplemental_summary["new_operations"] == 98,
                "supplemental operation census")
        summary = {
            "status": "PASS",
            "python": sys.version.split()[0],
            "optimized": bool(sys.flags.optimize),
            "manifest_files": manifest_count,
            "checks": checks,
            "main_circuits": prime["equations"],
            "exact_generic_norm": {
                k: v for k, v in norm.items()
                if k not in ["elapsed_seconds", "runtime_seconds"]
            },
            "direct": direct_summary,
            "supplemental": supplemental_summary,
            "scope": (
                "Exact finite artifacts, identities, and certificates. "
                "The unbounded arithmetic proofs and inherited logical "
                "calibrations remain the identified mathematical dependencies."
            )
        }
        if options.receipt:
            target = options.receipt.resolve()
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(json.dumps(summary, indent=2) + "\n")
        print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

