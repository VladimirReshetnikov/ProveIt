#!/usr/bin/env python3
"""Compile the exact decoder dependency closure and the uniform-clock extension.

Uses only the pinned repository's Lean sources and Lean 4.32.0's bundled library.
No mathlib or endpoint build is required. Every module is built from source.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

BASELINE = "2ca3a5c16f0876d2cab842056353c03a1ed2f5f0"


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args()
    repo, out = args.repo.resolve(), args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    src = repo / "Computability/BusyBeaver/Lean"
    packet = Path(__file__).resolve().parents[1]
    order, seen = [], set()

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        p = src / (module.replace(".", "/") + ".lean")
        for line in p.read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    if dep.startswith("BusyBeaver."):
                        visit(dep)
                    elif dep != "Init":
                        raise RuntimeError(f"Unexpected external import: {dep}")
        order.append((module, p, src))

    visit("BusyBeaver.ZFC.KDecoderPrefix215")
    order.append(("UniformDecoder", packet / "proofs/UniformDecoder.lean", packet / "proofs"))
    order.append(("UniformZipper", packet / "proofs/UniformZipper.lean", packet / "proofs"))
    env = dict(os.environ, LEAN_PATH=str(out))
    version = subprocess.run([args.lean, "--version"], check=True, text=True,
                             stdout=subprocess.PIPE).stdout.strip()
    head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], check=True,
                          text=True, stdout=subprocess.PIPE).stdout.strip()
    if head != BASELINE:
        raise RuntimeError(f"Expected {BASELINE}; got {head}")
    records = []
    for module, p, root in order:
        obj = out / (module.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        cmd = [args.lean, "--root=" + str(root), "-o", str(obj), str(p)]
        start = time.perf_counter()
        result = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        elapsed = time.perf_counter() - start
        log = out / (module.replace(".", "_") + ".log")
        log.write_text(result.stdout)
        rec = {"module": module, "source": str(p.relative_to(repo)) if p.is_relative_to(repo)
               else "proofs/" + p.name,
               "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
               "exit_code": result.returncode, "seconds": elapsed,
               "command": cmd, "log": log.name,
               "object_sha256": hashlib.sha256(obj.read_bytes()).hexdigest()
               if obj.exists() else None}
        records.append(rec)
        report = {"baseline": BASELINE, "compiler": version,
                  "scope": "23 original decoder/runtime modules plus UniformDecoder and UniformZipper; no endpoint rebuild",
                  "status": "PASS" if len(records) == len(order) and result.returncode == 0
                  else ("FAIL" if result.returncode else "IN_PROGRESS"), "modules": records}
        (out / "uniform_decoder_verification.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{module}: exit {result.returncode}, {elapsed:.3f}s", flush=True)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
