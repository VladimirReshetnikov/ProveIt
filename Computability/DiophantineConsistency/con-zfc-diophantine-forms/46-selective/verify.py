#!/usr/bin/env python3
"""Audit the complete release in an isolated, disposable copy.

Usage:
    python3 verify.py
    python3 verify.py --receipt RELEASE_AUDIT.json

Only the standard library is required. The real release is read, never rebuilt
in place. The optional receipt is the only intentional write outside the
temporary copy. Explicit exceptions, rather than assert statements, keep this
driver's checks active when it is itself invoked with python3 -O.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
PIN = "124c07c0b77a9e20e84676514d8b1ff78536ea3f"
MAIN_OUTPUTS = (
    "data/polynomial.json",
    "data/coefficient_recipes.json",
    "certificates/coefficient_bound.json",
    "certificates/degree.json",
    "certificates/metrics.json",
)
NINE_OUTPUTS = tuple(
    "nine/generated/selective_nine_" + domain + suffix + ".json"
    for domain in ("positive", "natural")
    for suffix in ("", "_degree_certificate")
)
MANIFEST_NAMES = ("MANIFEST.sha256", "SHA256SUMS", "SHA256SUMS.txt")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(data):
    return hashlib.sha1(
        b"blob " + str(len(data)).encode("ascii") + b"\0" + data
    ).hexdigest()


def local_file(root, name):
    """Resolve a manifest/provenance filename without permitting traversal."""
    require(isinstance(name, str) and name, "Empty or non-string filename")
    relative = PurePosixPath(name)
    require(not relative.is_absolute() and ".." not in relative.parts,
            "Unsafe relative filename: " + name)
    path = root.joinpath(*relative.parts)
    require(path.resolve().is_relative_to(root.resolve()),
            "Filename escapes the release: " + name)
    require(path.is_file(), "Missing release file: " + name)
    return path


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def tree_snapshot(root):
    """Detect any unintended writes to the original release, including caches."""
    return {
        path.relative_to(root).as_posix(): digest(path.read_bytes())
        for path in sorted(root.rglob("*")) if path.is_file()
    }


def check_provenance(root):
    sources = read_json(local_file(root, "SOURCES.json"))
    require(sources.get("commit") == PIN, "Unexpected imported source commit")
    require(sources.get("repository") == "VladimirReshetnikov/ProveIt",
            "Unexpected imported repository")
    rows = sources.get("sources")
    require(isinstance(rows, list) and rows, "Empty root source provenance")
    seen = set()
    for row in rows:
        name = row["local_path"]
        require(name not in seen, "Duplicate root source entry: " + name)
        seen.add(name)
        data = local_file(root, name).read_bytes()
        require(git_blob(data) == row["git_blob_sha1"],
                "Root source Git blob differs: " + name)
        if "sha256" in row:
            require(digest(data) == row["sha256"],
                    "Root source SHA256 differs: " + name)
        if "size_bytes" in row:
            require(len(data) == row["size_bytes"],
                    "Root source length differs: " + name)

    provenance = read_json(local_file(root, "upstream/SOURCE_PROVENANCE.json"))
    imported = provenance.get("sources")
    require(isinstance(imported, list) and imported,
            "Empty upstream source provenance")
    seen_upstream = set()
    for row in imported:
        name = "upstream/" + row["local_file"]
        require(name not in seen_upstream, "Duplicate upstream source entry: " + name)
        seen_upstream.add(name)
        require(row["source_commit"] == PIN,
                "Upstream source commit differs: " + name)
        data = local_file(root, name).read_bytes()
        require(len(data) == row["size_bytes"],
                "Upstream source length differs: " + name)
        require(git_blob(data) == row["git_blob_sha1"],
                "Upstream source Git blob differs: " + name)
        require(digest(data) == row["sha256"],
                "Upstream source SHA256 differs: " + name)
    result = {
        "status": "PASS", "commit": PIN,
        "root_entries": len(rows), "upstream_entries": len(imported),
        "distinct_files": len(seen | seen_upstream),
    }
    print("PASS imported provenance: {} root entries, {} upstream entries".format(
        len(rows), len(imported)), flush=True)
    return result


def check_manifests(root, skip):
    existing = [name for name in MANIFEST_NAMES if (root / name).is_file()]
    if skip:
        print("SKIP release checksum manifest (--skip-manifest)", flush=True)
        return {"status": "SKIPPED", "present": existing}
    if not existing:
        print("INFO release checksum manifest is not present", flush=True)
        return {"status": "NOT_PRESENT", "present": []}
    manifests = []
    for name in existing:
        entries = {}
        for number, line in enumerate((root / name).read_text(encoding="utf-8").splitlines(), 1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            match = re.fullmatch(r"([0-9a-fA-F]{64})[ \t]+\*?(.+)", line)
            require(match is not None,
                    "Malformed checksum line {} in {}".format(number, name))
            expected, filename = match.groups()
            filename = PurePosixPath(filename).as_posix()
            require(filename not in entries,
                    "Duplicate checksum entry in {}: {}".format(name, filename))
            data = local_file(root, filename).read_bytes()
            require(digest(data) == expected.lower(),
                    "Release checksum differs: " + filename)
            entries[filename] = expected.lower()
        require(entries, "Empty checksum manifest: " + name)
        manifests.append({"file": name, "entries": len(entries),
                          "sha256": digest((root / name).read_bytes())})
        print("PASS {}: {} file checksums".format(name, len(entries)), flush=True)
    return {"status": "PASS", "manifests": manifests}


def check_shared_inputs(root):
    for name in ("layout.json", "raw_recipes.json"):
        require(read_json(local_file(root, "data/" + name)) ==
                read_json(local_file(root, "nine/data/" + name)),
                "Ten-variable and nine-variable source data differ: " + name)
    ports = []
    for name in ("beta", "K", "MC", "MF_source"):
        filename = "coefficients/payloads/" + name + ".bin.gz"
        ten = gzip.decompress(local_file(root, filename).read_bytes())
        nine = gzip.decompress(local_file(root, "nine/" + filename).read_bytes())
        require(ten == nine, "Ten-variable and nine-variable native ports differ: " + name)
        ports.append({"port": name, "raw_bytes": len(ten), "sha256": digest(ten)})
    print("PASS shared layouts, recipes, and all four native ports", flush=True)
    return {"status": "PASS", "ports": ports}


def compare_json_outputs(root, original, filenames):
    for filename in filenames:
        require(read_json(local_file(root, filename)) == original[filename],
                "Rebuilt JSON differs from the delivered snapshot: " + filename)
    return list(filenames)


def run_gate(root, label, script, optimized=False, receipt=None):
    """Run one subprocess, recording hashes instead of forwarding large logs."""
    local_file(root, script)
    if receipt:
        # An old PASS receipt must not mask a verifier that stopped writing it.
        target = root / receipt
        if target.exists():
            target.unlink()
    command = [sys.executable]
    if optimized:
        command.append("-O")
    command.append(str(root / script))
    environment = os.environ.copy()
    environment.pop("PYTHONOPTIMIZE", None)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    started = time.monotonic()
    result = subprocess.run(command, cwd=root, env=environment,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    elapsed = time.monotonic() - started
    if result.returncode:
        tail = (result.stdout + b"\n" + result.stderr)[-6000:].decode("utf-8", errors="replace")
        raise RuntimeError("{} failed (exit {}):\n{}".format(label, result.returncode, tail))
    summary = {
        "label": label, "script": script,
        "mode": "-O" if optimized else "normal", "status": "PASS",
        "exit_code": result.returncode, "elapsed_seconds": round(elapsed, 3),
        "stdout_bytes": len(result.stdout), "stdout_sha256": digest(result.stdout),
        "stderr_bytes": len(result.stderr), "stderr_sha256": digest(result.stderr),
    }
    if receipt:
        path = local_file(root, receipt)
        value = read_json(path)
        require(isinstance(value, dict) and value.get("status") == "PASS",
                label + " did not produce a PASS receipt")
        summary["receipt"] = receipt
        summary["receipt_sha256"] = digest(path.read_bytes())
        summary["receipt_data"] = value
    print("PASS {} ({:.2f}s)".format(label, elapsed), flush=True)
    return summary


def audit(args):
    started = time.monotonic()
    unchanged_before = tree_snapshot(ROOT)
    report = {
        "schema": "proveit-selective-release-audit-v1", "status": "RUNNING",
        "source_commit": PIN,
        "driver_optimization_level": sys.flags.optimize,
        "python_version": sys.version,
        "scope": "Finite release reproduction and independent implementation checks; "
                 "the unbounded solvability theorems also use the accompanying "
                 "mathematical proofs and explicitly cited upstream theorems.",
    }
    report["provenance"] = check_provenance(ROOT)
    report["manifest"] = check_manifests(ROOT, args.skip_manifest)
    report["shared_inputs"] = check_shared_inputs(ROOT)
    original = {name: read_json(local_file(ROOT, name))
                for name in MAIN_OUTPUTS + NINE_OUTPUTS}
    gates = []
    with tempfile.TemporaryDirectory(prefix="proveit-selective-release-") as temporary:
        stage = Path(temporary) / "release"
        shutil.copytree(ROOT, stage, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        # Rebuilders run normally even if this driver was invoked with -O.
        main = run_gate(stage, "ten-variable rebuild", "code/build.py")
        main["equal_json_artifacts"] = compare_json_outputs(stage, original, MAIN_OUTPUTS)
        gates.append(main)
        print("PASS ten-variable rebuild: all 5 delivered JSON artifacts reproduced", flush=True)
        nine = run_gate(stage, "nine-variable rebuild", "nine/build_nine.py")
        nine["equal_json_artifacts"] = compare_json_outputs(stage, original, NINE_OUTPUTS)
        gates.append(nine)
        print("PASS nine-variable rebuild: all 4 delivered JSON artifacts reproduced", flush=True)

        audits = (
            ("ten-variable independent audit", "code/audit_candidate.py",
             "certificates/candidate_independent_audit.json"),
            ("nine-variable independent audit", "nine/verify_nine.py",
             "nine/generated/VERIFICATION.json"),
            ("74-operation independent audit", "short/verify_p74.py",
             "short/p74_audit.json"),
        )
        for label, script, receipt in audits:
            for optimized in (False, True):
                mode = "-O" if optimized else "normal"
                gates.append(run_gate(stage, label + " [" + mode + "]", script,
                                      optimized=optimized, receipt=receipt))
        gates.append(run_gate(stage, "native coefficient reconstruction [normal]",
                              "coefficients/reconstruct_native.py",
                              receipt="coefficients/REPRODUCTION.json"))
        for optimized in (False, True):
            mode = "-O" if optimized else "normal"
            gates.append(run_gate(stage, "coefficient adapter independent audit [" + mode + "]",
                                  "coefficient_adapter/audit_separated.py", optimized=optimized,
                                  receipt="coefficient_adapter/separated_audit.json"))

    unchanged_after = tree_snapshot(ROOT)
    require(unchanged_after == unchanged_before,
            "The original release changed while the audit was running; "
            "stop other edits and rerun before relying on the receipt")
    require(len(gates) == 11, "The required subprocess audit sequence is incomplete")
    report.update(status="PASS", subprocess_gates=gates,
                  subprocess_gate_count=len(gates),
                  reproduced_json_artifacts=list(MAIN_OUTPUTS + NINE_OUTPUTS),
                  original_release_unchanged=True,
                  original_file_count=len(unchanged_before),
                  elapsed_seconds=round(time.monotonic() - started, 3))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--receipt", type=Path, metavar="PATH",
                        help="write the final JSON summary to PATH (the only non-temporary write)")
    parser.add_argument("--skip-manifest", action="store_true",
                        help="skip existing release checksum manifests while preparing a new package")
    args = parser.parse_args()
    try:
        report = audit(args)
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as error:
        print("FAIL release audit: " + str(error), file=sys.stderr)
        return 1
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        print("PASS JSON receipt written: " + str(args.receipt), flush=True)
    print("PASS complete release audit: 11 subprocess gates, 9 reproduced JSON artifacts; "
          "original release unchanged", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
