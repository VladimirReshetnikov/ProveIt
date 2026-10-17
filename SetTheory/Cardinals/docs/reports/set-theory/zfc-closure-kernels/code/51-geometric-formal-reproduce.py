#!/usr/bin/env python3
"""Rebuild every vendored Lean dependency and research theorem from source.

No ProveIt checkout or cached .olean is needed.  Supply Lean 4.32.0:
    python reproduce.py --lean /path/to/lean
All imports are compiled into a fresh temporary directory unless --build-dir
is supplied.  A JSON report and complete module logs are written to --output.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


def main() -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--build-dir", type=Path)
    parser.add_argument("--output", type=Path, default=root / "verification")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if lean is None:
        parser.error("Lean executable not found; supply --lean /path/to/lean")
    manifest = json.loads((root / "manifest.json").read_text())
    for item in manifest["modules"]:
        source = root / item["source"]
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != item["sha256"]:
            raise ValueError(f"Source digest mismatch: {item['source']}")
    version = subprocess.run([lean, "--version"], text=True, capture_output=True, check=True).stdout.strip()
    if "version 4.32.0" not in version:
        parser.error(f"Expected Lean 4.32.0; found {version}")
    temporary = None
    if args.build_dir is None:
        temporary = tempfile.TemporaryDirectory(prefix="proveit-research-lean-")
        build = Path(temporary.name)
    else:
        build = args.build_dir.resolve()
        build.mkdir(parents=True, exist_ok=True)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["LEAN_PATH"] = str(build)
    report = {"lean_version": version, "source_commit": manifest["source_commit"],
              "all_modules_rebuilt_from_source": True, "modules": []}
    returncode = 0
    for item in manifest["modules"]:
        module = item["module"]
        source = root / item["source"]
        target = build / Path(*module.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [lean, "-o", str(target), str(source)]
        start = time.monotonic()
        result = subprocess.run(command, env=environment, text=True, capture_output=True)
        log = output / (module + ".log")
        log.write_text(result.stdout + result.stderr)
        row = {**item, "returncode": result.returncode, "seconds": time.monotonic() - start,
               "log": log.name, "command": command}
        report["modules"].append(row)
        print(f"{module}: {'PASS' if result.returncode == 0 else 'FAIL'}", flush=True)
        (output / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
        if result.returncode:
            print(result.stdout + result.stderr, flush=True)
            returncode = result.returncode
            break
    report["success"] = returncode == 0 and len(report["modules"]) == len(manifest["modules"])
    (output / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    if temporary is not None:
        temporary.cleanup()
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
