#!/usr/bin/env python3
"""Replay the pinned KSim refactor using Lean 4.32.0, without fetching anything.

Usage: python3 replay.py --repo /path/to/ProveIt --lean /path/to/lean --out /tmp/replay
The output directory must not already exist. Every baseline module is rebuilt;
the patched run reuses only the exact unchanged baseline dependency objects.
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


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--lean", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    pkg = Path(__file__).resolve().parent
    ledger = json.loads((pkg / "source-hashes.json").read_text())
    source_root = args.repo.resolve() / ledger["source_root"]
    args.out.mkdir(parents=True, exist_ok=False)
    out = args.out.resolve()
    lean = str(args.lean.resolve())
    compiler = subprocess.run([lean, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    if "version 4.32.0" not in compiler:
        raise SystemExit(f"Expected Lean 4.32.0; got {compiler}")
    for module, expected in ledger["modules"].items():
        path = source_root / (module.replace(".", "/") + ".lean")
        actual = digest(path)
        if actual != expected:
            raise SystemExit(f"Source mismatch: {path}\nExpected {expected}\nObserved {actual}")
    results: dict = {"pin": ledger["pin"], "compiler": compiler, "runs": []}
    receipt = out / "receipt.json"

    def compile_at(root: Path, module: str, lane: str) -> None:
        src = root / (module.replace(".", "/") + ".lean")
        env = dict(os.environ, LEAN_PATH=str(root))
        start = time.perf_counter()
        proc = subprocess.run([lean, "-o", str(src.with_suffix(".olean")), str(src)],
                              cwd=root, env=env, capture_output=True, text=True)
        entry = {"lane": lane, "module": module, "source_sha256": digest(src),
                 "exit_code": proc.returncode, "seconds": time.perf_counter() - start,
                 "output": proc.stdout + proc.stderr}
        results["runs"].append(entry)
        receipt.write_text(json.dumps(results, indent=2) + "\n")
        print(f"{lane}: {module}: exit {proc.returncode}", flush=True)
        if proc.returncode:
            raise SystemExit(entry["output"])

    baseline = out / "baseline"
    for module in ledger["modules"]:
        rel = Path(module.replace(".", "/") + ".lean")
        dst = baseline / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_root / rel, dst)
        compile_at(baseline, module, "baseline")
    audit = """import BusyBeaver.ZFC.KSim
#print axioms SetTheory.BusyBeaver.ZFC.KSim.halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.KSim.sim_step
"""
    (baseline / "Audit.lean").write_text(audit)
    compile_at(baseline, "Audit", "baseline")

    patched = out / "patched"
    shutil.copytree(baseline, patched)
    for module in ledger["modules"]:
        if module != "BusyBeaver.ZFC.KSim":
            results["runs"].append({"lane": "patched", "module": module,
                                     "reused_exact_baseline_object": True,
                                     "source_sha256": ledger["modules"][module]})
    for name in ("TerminationTransport", "TerminationTransportK", "ProgressCounterexamples", "KSim"):
        module = "BusyBeaver.ZFC." + name
        rel = Path(module.replace(".", "/") + ".lean")
        shutil.copy2(pkg / "lean" / rel, patched / rel)
        compile_at(patched, module, "patched")
    compile_at(patched, "Audit", "patched")
    results["complete"] = True
    receipt.write_text(json.dumps(results, indent=2) + "\n")
    print(receipt, flush=True)


if __name__ == "__main__":
    main()
