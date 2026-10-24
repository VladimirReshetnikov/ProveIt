#!/usr/bin/env python3
"""Rebuild and audit the release in an isolated temporary copy; stdlib only.

The unbounded semantic proof is in report/parity-norms.tex. This program checks
finite coefficient reconstruction, polynomial identities, literal programs and
degree certificates. It neither tests nor assumes ZFC consistency.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest():
    manifest = ROOT / "SHA256SUMS"
    if not manifest.exists():
        return {"status": "not yet present during release assembly", "files": 0}
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        path = (ROOT / relative).resolve()
        require(path.is_relative_to(ROOT), "manifest path escapes release")
        require(path.is_file(), "missing release file: " + relative)
        require(digest(path) == expected, "release hash mismatch: " + relative)
        count += 1
    return {"status": "PASS", "files": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="optional receipt path")
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), "Python 3.10 or later is required")
    require(__debug__, "run this release verifier without -O; inherited recipe uses assertions")
    started = time.monotonic()
    manifest = verify_manifest()

    patterns = ("parity*.json", "centered*.json", "norm*.json")
    fixed = {p.name: digest(p) for pattern in patterns for p in ROOT.glob(pattern)}
    for name in ("abstract_norm5_dag.json", "COMPACT_METRICS.json",
                 "NORM_FAMILY_METRICS.json", "DEGREE_CERTIFICATES.json"):
        fixed[name] = digest(ROOT / name)

    commands = [
        "coefficients/verify.py",
        "build.py",
        "build_norm_family.py",
        "compact_norm.py",
        "audit.py",
        "audit_norm_family.py",
        "audit_shift.py",
        "audit_compact_kernel.py",
        "independent_checks.py",
        "independent_graph_audit.py",
        "independent_compact_audit.py",
    ]
    stages = []
    with tempfile.TemporaryDirectory(prefix="proveit-parity-replay-") as tmp:
        work = Path(tmp)
        for pattern in ("*.py", "*.json"):
            for path in ROOT.glob(pattern):
                shutil.copy2(path, work / path.name)
        for name in ("coefficients", "inherited", "parent"):
            shutil.copytree(ROOT / name, work / name,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        environment = dict(os.environ)
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        for index, script in enumerate(commands, 1):
            print(f"[{index}/{len(commands)}] {script}", flush=True)
            stage_started = time.monotonic()
            process = subprocess.run([sys.executable, script], cwd=work,
                                     env=environment, text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if process.returncode:
                print(process.stdout, file=sys.stderr)
                raise RuntimeError(f"{script} exited with {process.returncode}")
            stages.append({"script": script, "status": "PASS",
                           "seconds": round(time.monotonic() - stage_started, 3),
                           "stdout_sha256": hashlib.sha256(process.stdout.encode()).hexdigest()})
        for name, expected in sorted(fixed.items()):
            require(digest(work / name) == expected,
                    "regenerated specification is not byte-identical: " + name)
        primary = json.loads((work / "parity13_shifted_dag.json").read_text())
        compact = json.loads((work / "COMPACT_INDEPENDENT_AUDIT.json").read_text())
        shift = json.loads((work / "SHIFT_AUDIT.json").read_text())
        coefficients = json.loads((work / "coefficients/VERIFICATION.json").read_text())
        require(len(primary["variables"]) == 13, "primary variable count")
        require(primary["exact_degree"] == 1392, "primary exact degree")
        require(primary["operations"] == 211, "primary operation count")
        require(primary["counts"] == {"add": 51, "sub": 31, "mul": 129},
                "primary operation census")
        require(shift["leading_coefficient_mod_prime"] == 756708762,
                "primary exact-degree witness")
        require(compact["status"] == coefficients["status"] == "PASS",
                "independent or coefficient audit status")

    receipt = {
        "status": "PASS",
        "python_version": sys.version.split()[0],
        "manifest": manifest,
        "stages": stages,
        "byte_identical_rebuilt_specifications": len(fixed),
        "primary": {"file": "parity13_shifted_dag.json",
                    "sha256": digest(ROOT / "parity13_shifted_dag.json"),
                    "integer_variables": 13, "exact_total_degree": 1392,
                    "operations": 211, "counts": primary["counts"],
                    "degree_witness_mod_1000000007": 756708762},
        "fixed_coefficient_raw_bytes": coefficients["raw_bytes"],
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "scope": "Finite exact algebra and coefficient reconstruction, literal DAGs, degrees and supplementary diagnostics. The report supplies the unbounded arithmetic reduction; the native semantic theorem is inherited.",
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.resolve().write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
