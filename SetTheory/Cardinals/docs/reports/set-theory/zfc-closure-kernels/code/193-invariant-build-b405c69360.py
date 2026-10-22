#!/usr/bin/env python3
"""Rebuild either proposal in an isolated output directory, without changing ProveIt.

Requires a local ProveIt checkout with the pinned dependency bytes and Lean 4.32.0.
No network access, Lake build, executable certificates, or repository writes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    return [item for line in path.read_text().splitlines()
            if line.startswith("import ") for item in line[7:].split()
            if item.startswith("BusyBeaver.")]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--lean", required=True, type=Path)
    ap.add_argument("--variant", choices=["minimal", "terminal-drain"], default="minimal")
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    repo = args.repo.resolve()
    lean = args.lean.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source_root = repo / "Computability/BusyBeaver/Lean"
    overlay = here / args.variant
    pins = json.loads((here / "verification/original-source-sha256.json").read_text())
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "version 4.32.0" not in version:
        raise SystemExit(f"Expected Lean 4.32.0, got {version!r}")
    targets = (["BusyBeaver.ZFC.DenseBridgeAudit"] if args.variant == "minimal" else
               ["BusyBeaver.ZFC.KDenseBridge", "BusyBeaver.ZFC.KSim",
                "BusyBeaver.ZFC.TerminalDrainExamples"])
    pending, sources, order = set(), {}, []

    def visit(module):
        if module in sources:
            return
        if module in pending:
            raise RuntimeError(f"Import cycle at {module}")
        pending.add(module)
        rel = Path(*module.split(".")).with_suffix(".lean")
        source = overlay / rel
        origin = "proposal"
        if not source.exists():
            source = source_root / rel
            origin = "repository"
            key = str(source.relative_to(repo))
            if key not in pins or sha(source) != pins[key]:
                raise SystemExit(f"Original dependency does not match recorded source: {key}")
        ds = imports(source)
        for dep in ds:
            visit(dep)
        pending.remove(module)
        sources[module] = (source, origin, ds)
        order.append(module)

    for target in targets:
        visit(target)
    build = out / "objects"
    logs = out / "logs"
    build.mkdir(exist_ok=True)
    logs.mkdir(exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(build))
    records = []
    for module in order:
        source, origin, ds = sources[module]
        obj = (build / Path(*module.split("."))).with_suffix(".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + ".log")
        cmd = [str(lean), "-o", str(obj), str(source)]
        start = time.monotonic()
        proc = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, check=False)
        log.write_text(proc.stdout)
        record = {"module": module, "origin": origin, "source": str(source),
                  "source_sha256": sha(source), "imports": ds,
                  "exit_code": proc.returncode, "elapsed_seconds": time.monotonic() - start,
                  "warning_count": proc.stdout.count("warning:"),
                  "log": str(log), "log_sha256": sha(log),
                  "object_sha256": sha(obj) if proc.returncode == 0 else None}
        records.append(record)
        print(f"{module}: exit {proc.returncode}", flush=True)
        receipt = {"base_commit": "57541fe0cfe3af62b4cb58747d8d1d7c16b338d5",
                   "variant": args.variant, "lean_version": version,
                   "target_modules": targets, "records": records,
                   "complete": len(records) == len(order) and proc.returncode == 0}
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        if (proc.returncode != 0 or "sorryAx" in proc.stdout or
                (origin == "proposal" and "warning:" in proc.stdout)):
            raise SystemExit(f"Review {log}: compile failed, sorryAx, or proposed-module warning found")


if __name__ == "__main__":
    main()
