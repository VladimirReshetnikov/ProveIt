#!/usr/bin/env python3
"""Run the finite release audits. Python 3.10+, standard library only.

These checks certify finite algebra, literal circuits, and data bindings.
The ordinary unbounded proofs and inherited calibration are separate.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
JOBS = [
    ("nine", "nine/verify.py"),
    ("nine_independent", "nine/certificates/audit_h1868_degree.py"),
    ("pell_saturation", "nine/certificates/check_saturation.py"),
    ("positive11", "positive11/verify.py"),
    ("integer", "integer/verify.py"),
]


def manifest_check():
    path = ROOT / "MANIFEST.sha256"
    if not path.exists():
        return {"status": "not present in working draft", "checked": 0}
    count = 0
    for line in path.read_text().splitlines():
        digest, name = line.split("  ", 1)
        p = ROOT / name
        if p.is_symlink() or not p.is_file():
            raise RuntimeError("Missing or nonregular release member: " + name)
        if hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            raise RuntimeError("Release hash mismatch: " + name)
        count += 1
    return {"status": "PASS", "checked": count}


def run_one(name, script, optimized, outdir):
    start = time.monotonic()
    label = name + ("_optimized" if optimized else "_normal")
    args = [sys.executable, "-B"] + (["-O"] if optimized else []) + [str(ROOT / script)]
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    proc = subprocess.run(args, cwd=ROOT, env=env, text=True, capture_output=True)
    (outdir / (label + ".stdout.txt")).write_text(proc.stdout)
    (outdir / (label + ".stderr.txt")).write_text(proc.stderr)
    result = {
        "audit": name, "optimization": int(optimized),
        "status": "PASS" if proc.returncode == 0 else "FAIL",
        "exit_code": proc.returncode,
        "seconds": round(time.monotonic() - start, 3),
        "script": script,
        "script_sha256": hashlib.sha256((ROOT / script).read_bytes()).hexdigest(),
        "stdout": str((outdir / (label + ".stdout.txt")).relative_to(ROOT)),
        "stderr": str((outdir / (label + ".stderr.txt")).relative_to(ROOT)),
    }
    print(label + ": " + result["status"], flush=True)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--optimized", action="store_true", help="run with Python -O")
    parser.add_argument("--both", action="store_true", help="normal then optimized audits")
    parser.add_argument("--workers", type=int, default=3)
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")
    integrity = manifest_check()
    outdir = ROOT / "verification"
    outdir.mkdir(exist_ok=True)
    modes = [False, True] if args.both else [args.optimized]
    results = []
    # Modes are sequential because a few inherited audit receipts have fixed names.
    for mode in modes:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            pending = [pool.submit(run_one, n, p, mode, outdir) for n, p in JOBS]
            for future in as_completed(pending):
                results.append(future.result())
    ok = all(r["status"] == "PASS" for r in results)
    report = {
        "status": "PASS" if ok else "FAIL", "python": sys.version,
        "release_integrity": integrity, "audits": results,
        "scope": "Finite exact identities, coefficient/data bindings, degree certificates, literal DAGs, and explicitly labeled diagnostics. No consistency assertion or end-to-end internal-ZFC formal certificate.",
    }
    name = "RELEASE_CHECKS_BOTH.json" if args.both else (
        "RELEASE_CHECKS_OPTIMIZED.json" if args.optimized else "RELEASE_CHECKS.json")
    (outdir / name).write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "audits": len(results)}, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
