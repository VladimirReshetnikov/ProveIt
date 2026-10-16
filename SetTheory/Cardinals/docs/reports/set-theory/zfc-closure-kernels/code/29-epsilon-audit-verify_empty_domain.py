#!/usr/bin/env python3
"""Rebuild the small Code254 dependency closure and check its domain repair.

Usage: python3 verify_empty_domain.py --lean /path/to/lean
Requires the pinned Lean 4.32.0 toolchain and the adjacent lean_src directory.
This performs a serial source rebuild; no pre-existing project oleans are used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

PIN = "d74c63b0c8d4f35597f1bd5976d941b9f104f94e"
MODULES = [
    "FirstOrder/Fol.lean",
    "BusyBeaver/ZFC/Kalmar.lean",
    "BusyBeaver/ZFC/TarskiCalculus.lean",
    "BusyBeaver/ZFC/TarskiDerived.lean",
    "BusyBeaver/ZFC/TarskiLeibniz.lean",
    "BusyBeaver/ZFC/TarskiClean.lean",
    "BusyBeaver/ZFC/TarskiComplete.lean",
    "BusyBeaver/ZFC/Lukasiewicz.lean",
    "BusyBeaver/ZFC/TarskiFalsity.lean",
    "BusyBeaver/ZFC/Code254.lean",
    "EmptyDomainRepair.lean",
]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    source = root / "lean_src"
    manifest = json.loads((root / "source-manifest.json").read_text())
    for row in manifest["files"]:
        data = (root / row["path"]).read_bytes()
        if hashlib.sha256(data).hexdigest() != row["sha256"]:
            raise SystemExit("Source SHA-256 mismatch: " + row["path"])
        expected_blob = row.get("upstream_git_blob_sha1")
        if expected_blob:
            actual_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if actual_blob != expected_blob:
                raise SystemExit("Pinned Git blob mismatch: " + row["path"])
    build = Path(tempfile.mkdtemp(prefix="code254-domain-check-"))
    out = args.output or root / "empty-domain-verification.json"
    env = dict(os.environ)
    env["LEAN_PATH"] = str(build)
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if "4.32.0" not in version:
        raise SystemExit("This audit is pinned to Lean 4.32.0; observed " + version)
    records = []
    print(version, flush=True)
    for module in MODULES:
        path = source / module
        obj = build / Path(module).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        proc = subprocess.run([args.lean, "-o", str(obj), module],
                              cwd=source, env=env, capture_output=True,
                              text=True, timeout=240)
        output = proc.stdout + proc.stderr
        record = {"module": module, "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                  "returncode": proc.returncode, "output": output}
        records.append(record)
        print(module + ": exit " + str(proc.returncode), flush=True)
        if proc.returncode or "sorryAx" in output or "declaration uses 'sorry'" in output:
            print(output, flush=True)
            raise SystemExit(proc.returncode or 1)
    pure = root / "EmptyDomainAudit.lean"
    proc = subprocess.run([args.lean, str(pure)], cwd=root, env=env,
                          capture_output=True, text=True, timeout=60)
    records.append({"module": pure.name,
                    "source_sha256": hashlib.sha256(pure.read_bytes()).hexdigest(),
                    "returncode": proc.returncode, "output": proc.stdout + proc.stderr})
    if proc.returncode:
        print(proc.stdout + proc.stderr)
        raise SystemExit(proc.returncode)
    data = {"upstream_commit": PIN, "lean_version": version, "serial_fresh_rebuild": True, "pinned_git_blob_bytes_verified": True,
            "modules": records, "build_directory": str(build)}
    out.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    print(records[-2]["output"], end="", flush=True)
    print(records[-1]["output"], end="", flush=True)
    print("PASS: 11 dependency/repair modules plus standalone audit; " + str(out), flush=True)

if __name__ == "__main__":
    main()

