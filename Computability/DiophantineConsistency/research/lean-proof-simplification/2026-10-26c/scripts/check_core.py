#!/usr/bin/env python3
"""Replay the package's small checked Lean examples without modifying ProveIt.

--repo optionally adds the repository's already-built Mathlib environment and
checks RowOperations. No dependency download, Lake update, or repository edit
is performed. Larger candidates are deliberately not represented as checked.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

PIN = "60e9c5d620c6c387d932876cfa2d9376f64ea56c"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default=shutil.which("lean") or "lean")
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--repo", type=Path)
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--memory-mb", type=int, default=2048)
    args = ap.parse_args()
    package = Path(__file__).resolve().parent.parent
    source = package / "lean" / "checked"
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    oleans = output / "olean"
    oleans.mkdir(exist_ok=True)
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if "version 4.32.0," not in version:
        raise SystemExit(f"Expected Lean 4.32.0, found: {version}")
    paths = [str(oleans)]
    if args.repo:
        repo = args.repo.resolve()
        commit = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
        if commit != PIN:
            raise SystemExit(f"Expected repository commit {PIN}, found {commit}")
        paths.append(str(repo / ".lake/build/lib/lean"))
        paths.extend(str(p) for p in sorted((repo / ".lake/packages").glob("*/.lake/build/lib/lean")))
    env = dict(os.environ)
    env["LEAN_PATH"] = os.pathsep.join(paths)
    jobs = ["ScannerCore", "ScannerAudit", "LookupCleanup", "HalfRadix", "AssignmentTransportCore"]
    if args.repo:
        jobs.append("RowOperations")
    results = []
    for name in jobs:
        path = source / (name + ".lean")
        argv = [args.lean, "-j1", f"-M{args.memory_mb}", "-R", str(source)]
        if name == "ScannerCore":
            argv += ["-o", str(oleans / "ScannerCore.olean")]
        argv.append(str(path))
        start = time.monotonic()
        timed_out = False
        try:
            p = subprocess.run(argv, cwd=source, env=env, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=args.timeout)
            code, log = p.returncode, p.stdout
        except subprocess.TimeoutExpired as e:
            code, timed_out = None, True
            log = e.stdout or ""
            if isinstance(log, bytes): log = log.decode(errors="replace")
            log += "\nTIMEOUT\n"
        (output / (name + ".log")).write_text(log)
        row = dict(file=str(path.relative_to(package)),
                   sha256=hashlib.sha256(path.read_bytes()).hexdigest(), command=argv,
                   exit_code=code, timed_out=timed_out,
                   elapsed_seconds=round(time.monotonic()-start, 3),
                   status="PASS" if code == 0 else "NOT_VERIFIED")
        results.append(row)
        print(f"{name}: {row['status']}", flush=True)
        if code != 0: break
    report = dict(lean_version=version, results=results,
                  note="Elapsed time is a replay receipt, not a controlled benchmark.")
    (output / "verification.json").write_text(json.dumps(report, indent=2)+"\n")
    if len(results) != len(jobs) or any(r["exit_code"] != 0 for r in results):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
