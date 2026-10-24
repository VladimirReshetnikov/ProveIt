#!/usr/bin/env python3
"""Offline integrated checks. No proof of consistency is attempted."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    path = ROOT / "MANIFEST.sha256"
    if not path.exists():
        return {"present": False, "files": 0}
    count = 0
    for line in path.read_text().splitlines():
        expected, relative = line.split("  ", 1)
        p = ROOT / relative
        require(p.resolve().is_relative_to(ROOT), "manifest path escapes release")
        require(p.is_file() and digest(p) == expected, "manifest mismatch: " + relative)
        count += 1
    return {"present": True, "files": count}


def authenticate_nine_sources():
    records = json.loads((ROOT / "nine/SOURCE_PINS.json").read_text())["retained_provenance"]
    for rec in records:
        p = ROOT / "nine" / rec["file"]
        require(p.is_file(), "missing retained source " + rec["file"])
        require(p.stat().st_size == rec["bytes"] and digest(p) == rec["sha256"],
                "retained source mismatch " + rec["file"])
    pins = json.loads((ROOT / "provenance/DIRECT_INPUTS.json").read_text())
    for rec in pins["files"]:
        p = ROOT / rec["package_path"]
        require(digest(p) == rec["sha256"], "frozen direct input mismatch")
    return len(records) + len(pins["files"])


def run(relative, optimized=False):
    script = ROOT / relative
    args = [sys.executable] + (["-O"] if optimized else []) + [str(script)]
    done = subprocess.run(args, cwd=script.parent, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if done.returncode:
        sys.stderr.write(done.stdout[-8000:] + done.stderr[-8000:])
        raise RuntimeError("component failed: " + relative)
    print(("PASS -O " if optimized else "PASS    ") + relative, flush=True)
    return {"script": relative, "optimized": optimized, "status": "PASS"}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest-only", action="store_true")
    options = ap.parse_args()
    manifest = check_manifest()
    if options.manifest_only:
        require(manifest["present"], "manifest is absent")
        print(json.dumps({"status": "PASS", "manifest": manifest}, indent=2))
        return
    sources = authenticate_nine_sources()
    rows = []
    for relative in ("integer/verify.py", "nine/verify.py", "nine/reconstruct_fixed.py",
                     "alternative/verify.py"):
        for optimized in (False, True):
            rows.append(run(relative, optimized))
    metrics = {
        "integer": json.loads((ROOT / "integer/VERIFICATION.json").read_text())["packets"],
        "nine": json.loads((ROOT / "nine/VERIFICATION.json").read_text())["degrees"],
    }
    result = {
        "status": "PASS",
        "frozen_commit": "c1a102936aca437e9999530a0111e6ddab56dc6d",
        "additional_source_pins_checked": sources,
        "checks": rows,
        "metrics": metrics,
        "scope": "Exact finite algebra, data, circuits, degree certificates and diagnostics. "
                 "Unbounded new proofs are in the report. Native/refutation calibration is inherited; "
                 "no end-to-end proof-assistant or internal-ZFC certificate is asserted.",
    }
    (ROOT / "verification/RELEASE_CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: all eight component runs, complete coefficient reconstruction, and frozen source checks.")


if __name__ == "__main__":
    main()
