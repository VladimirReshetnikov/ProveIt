#!/usr/bin/env python3
"""Reproduce the five standalone Lean checks using a supplied ProveIt checkout.

This is a portable reproduction workflow, not the command used for the report's
original validation. It does not apply production patches. Lake may populate the
checkout's .lake build/dependency directories according to its normal behavior.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

PACKAGE = Path(__file__).resolve().parents[1]
FILES = (
    "CertificateReuse.lean", "BoundaryConservation.lean", "ShiftedNumerator.lean",
    "ConstantPredicate.lean", "ConstantPredicatePost01.lean",
)


def now():
    return datetime.now(timezone.utc).isoformat()


def mathlib_pin(manifest):
    entries = [p for p in manifest["packages"] if p.get("name") == "mathlib"]
    if len(entries) != 1:
        raise ValueError("Manifest must contain exactly one mathlib package.")
    entry = entries[0]
    if entry.get("type") != "git" or not entry.get("url") or not entry.get("rev"):
        raise ValueError("Mathlib must have an explicit Git URL and pinned revision.")
    return {key: entry.get(key) for key in ("type", "url", "rev", "subDir")}


def run(argv, cwd, logfile):
    print("Running: " + " ".join(str(x) for x in argv), flush=True)
    start = time.monotonic()
    try:
        process = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT, check=False)
        output, code = process.stdout, process.returncode
    except OSError as exc:
        output, code = (str(exc) + "\n").encode(), 127
    logfile.write_bytes(output)
    if output:
        sys.stdout.buffer.write(output)
        sys.stdout.buffer.flush()
    return {"command": [str(x) for x in argv], "cwd": str(cwd),
            "exit_code": code, "elapsed_seconds": time.monotonic() - start,
            "log": str(logfile)}


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Example: python scripts/check_lean.py --repo /path/to/ProveIt "
               "--output /path/to/new-lean-check.json\n"
               "Use the repository root containing lean-toolchain and lake-manifest.json.\n"
               "Logs accompany the JSON receipt. Default output uses tempfile and honors TMPDIR.\n"
               "A successful run checks these standalone examples; it does not validate all production patches.")
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--lake", default="lake", help="Lake executable (default: lake on PATH)")
    parser.add_argument("--output", type=Path, help="New JSON receipt; refuses to overwrite an existing result")
    args = parser.parse_args()
    repo = args.repo.expanduser().resolve()
    report = (args.output.expanduser().resolve() if args.output else
              Path(tempfile.mkdtemp(prefix="proveit-lean-check-")) / "result.json")
    logs = report.with_name(report.stem + ".logs")
    if report.exists() or logs.exists():
        parser.error("Output receipt or its log directory already exists; choose a fresh --output.")
    report.parent.mkdir(parents=True, exist_ok=True)
    logs.mkdir()
    receipt = {"purpose": "new portable reproduction run, not original validation command",
               "started_utc": now(), "repo": str(repo), "package": str(PACKAGE),
               "files": [{"file": name, "status": "not-run", "exit_code": None} for name in FILES]}
    result = 2
    try:
        reference = PACKAGE / "reference"
        expected_toolchain = (reference / "lean-toolchain").read_text().strip()
        actual_toolchain = (repo / "lean-toolchain").read_text().strip()
        expected_mathlib = mathlib_pin(json.loads((reference / "lake-manifest.json").read_text()))
        actual_mathlib = mathlib_pin(json.loads((repo / "lake-manifest.json").read_text()))
        receipt["pins"] = {"expected_toolchain": expected_toolchain, "actual_toolchain": actual_toolchain,
                           "expected_mathlib": expected_mathlib, "actual_mathlib": actual_mathlib}
        if not expected_toolchain or actual_toolchain != expected_toolchain:
            raise ValueError("lean-toolchain does not match package/reference/lean-toolchain.")
        if actual_mathlib != expected_mathlib:
            raise ValueError("Mathlib Git pin does not match package/reference/lake-manifest.json.")
        lake = shutil.which(args.lake)
        if lake is None:
            raise ValueError("Lake was not found. Supply the project's Lake executable with --lake.")
        for item in receipt["files"]:
            source = PACKAGE / "lean" / item["file"]
            item["sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        build = run([lake, "build", "DiophantineConsistency.ScalarPRCode"], repo, logs / "build.log")
        receipt["build"] = build
        if build["exit_code"] != 0:
            for item in receipt["files"]:
                item.update(status="skipped", reason="required ScalarPRCode build failed")
            result = 1
        else:
            result = 0
            for item in receipt["files"]:
                checked = run([lake, "env", "lean", str(PACKAGE / "lean" / item["file"])],
                              repo, logs / (Path(item["file"]).stem + ".log"))
                item.update(checked)
                item["status"] = "passed" if checked["exit_code"] == 0 else "failed"
                if checked["exit_code"] != 0:
                    result = 1
        receipt["status"] = "passed" if result == 0 else "failed"
    except (OSError, ValueError, KeyError, TypeError) as exc:
        receipt.update(status="preflight-failed", error=str(exc))
        print("Error: " + str(exc), file=sys.stderr)
    finally:
        receipt.update(finished_utc=now(), exit_code=result)
        report.write_text(json.dumps(receipt, indent=2) + "\n")
        print("Receipt: " + str(report), flush=True)
    return result


if __name__ == "__main__":
    sys.exit(main())
