#!/usr/bin/env python3
"""Replay the delivered exact checks offline in normal and optimized Python."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = (
    "verify_k4_certificate.py",
    "audit_global_schedule.py",
    "verify_comparisons.py",
    "verify_adaptive_four.py",
    "verify_adaptive_separator.py",
)


def verify_manifest():
    path = ROOT / "MANIFEST.sha256.json"
    if not path.exists():
        return {"status": "not present during initial authoring"}
    manifest = json.loads(path.read_text())
    for name, expected in manifest["files"].items():
        target = ROOT / name
        if not target.is_file():
            raise RuntimeError(f"Missing delivered file: {name}")
        digest = hashlib.sha256(target.read_bytes()).hexdigest()
        if digest != expected:
            raise RuntimeError(f"Delivered file has changed: {name}")
    return {"status": "passed", "file_count": len(manifest["files"])}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=ROOT / "replay_results")
    args = parser.parse_args()
    integrity = verify_manifest()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    summaries = []
    for script in CHECKS:
        values = []
        for optimized in (False, True):
            command = [sys.executable]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / "code" / script))
            completed = subprocess.run(command, cwd=ROOT / "code",
                                       check=True, capture_output=True, text=True)
            result = json.loads(completed.stdout)
            if result.get("status") != "passed":
                raise RuntimeError(f"Check did not report success: {script}")
            values.append(result)
            suffix = "_optimized" if optimized else ""
            (out / (Path(script).stem + suffix + ".json")).write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n")
        if values[0] != values[1]:
            raise RuntimeError(f"Normal and optimized results differ: {script}")
        summaries.append({"check": script, "normal": "passed", "optimized": "passed",
                          "parsed_outputs_identical": True})
    summary = {"status": "passed", "integrity": integrity, "checks": summaries,
               "scope": "Exact finite checks and scalar certificates; no full SAT solver or formal build."}
    (out / "REPLAY_SUMMARY.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
