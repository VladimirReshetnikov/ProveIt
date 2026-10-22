#!/usr/bin/env python3
"""Compile the PowerSets extraction and audit its exact source dependency cut.

Usage: python3 verify.py --repo PATH --lean /path/to/lean [--compile]
Uses the repository's pinned lean-toolchain, no network or package downloads.
The input checkout is never modified. Build products live under verification/.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import tomllib


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--compile", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    here = Path(__file__).resolve().parent
    overlay = here / "refactor"
    evidence = here / "verification"
    evidence.mkdir(exist_ok=True)
    config = tomllib.loads((repo / "lakefile.toml").read_text())
    roots = list(dict.fromkeys(repo / spec.get("srcDir", ".") for spec in config["lean_lib"]))
    cache: dict[tuple[str, bool], tuple[Path | None, bytes, list[str]]] = {}

    def source(module: str, modified: bool):
        key = module, modified
        if key in cache:
            return cache[key]
        relative = Path(module.replace(".", "/") + ".lean")
        candidates = ([overlay / relative] if modified else []) + [root / relative for root in roots]
        path = next((p for p in candidates if p.is_file()), None)
        data = path.read_bytes() if path else b""
        imports = re.findall(r"^import\s+([\w.]+)", data.decode(), re.M)
        cache[key] = path, data, imports
        return cache[key]

    def closure(targets: list[str], modified: bool):
        ordered: list[str] = []
        active: set[str] = set()
        seen: set[str] = set()

        def visit(module: str):
            if module in seen:
                return
            if module in active:
                raise ValueError(f"Cyclic imports at {module}")
            active.add(module)
            for dependency in source(module, modified)[2]:
                visit(dependency)
            active.remove(module)
            seen.add(module)
            ordered.append(module)

        for target in targets:
            visit(target)
        return ordered

    endpoint = "BusyBeaver.ZFC.KEndpoint215"
    before = closure([endpoint], False)
    after = closure([endpoint], True)
    project_before = {m for m in before if source(m, False)[0]}
    project_after = {m for m in after if source(m, True)[0]}
    removed = sorted(project_before - project_after)
    added = sorted(project_after - project_before)
    missing_before = sorted(set(before) - project_before)
    missing_after = sorted(set(after) - project_after)
    allowed_external = {"Init", "Std", "Lean"}
    bad_missing = (set(missing_before) | set(missing_after)) - allowed_external
    if bad_missing:
        raise ValueError(f"Cannot make exact closure claim; missing sources: {sorted(bad_missing)}")
    metrics = {
        "baseline_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip(),
        "lean_toolchain": (repo / "lean-toolchain").read_text().strip(),
        "method": "Transitive syntactic import closure; project sources resolved using lakefile.toml srcDir entries.",
        "endpoint": endpoint,
        "before_modules": len(project_before),
        "after_modules": len(project_after),
        "before_bytes": sum(len(source(m, False)[1]) for m in project_before),
        "after_bytes": sum(len(source(m, True)[1]) for m in project_after),
        "removed": [{"module": m, "path": str(source(m, False)[0].relative_to(repo)),
                     "bytes": len(source(m, False)[1]), "sha256": sha256(source(m, False)[1])} for m in removed],
        "added": [{"module": m, "bytes": len(source(m, True)[1]), "sha256": sha256(source(m, True)[1])} for m in added],
        "external_modules": missing_after,
        "before_closure": sorted(project_before),
        "after_closure": sorted(project_after),
        "note": "Source/import census only. No complete endpoint recompilation or build-speed claim.",
    }
    (evidence / "closure_metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    print(json.dumps({k:metrics[k] for k in ["before_modules", "after_modules", "before_bytes", "after_bytes", "removed", "added"]}, indent=2), flush=True)

    old_psc = source("BusyBeaver.ZFC.PSCCalibration", False)[1].decode()
    new_psc = source("BusyBeaver.ZFC.PSCCalibration", True)[1].decode()
    new_power = source("BusyBeaver.ZFC.PowerSets", True)[1].decode()
    old_wf = source("BusyBeaver.ZFC.WFModelCore", False)[1].decode()
    new_wf = source("BusyBeaver.ZFC.WFModelCore", True)[1].decode()
    declaration = "def PowerSets (mem : V → V → Prop) : Prop :=\n  ∀ a, ∃ p, ∀ y, mem y p ↔ SetTheory.Sub mem y a\n"
    assert old_psc.count(declaration) == 1 and new_power.count(declaration) == 1
    assert old_psc.replace(declaration + "\n", "").replace(
        "import BusyBeaver.ZFC.DefinableClosure\n",
        "import BusyBeaver.ZFC.DefinableClosure\nimport BusyBeaver.ZFC.PowerSets\n", 1) == new_psc
    assert old_wf.replace("import BusyBeaver.ZFC.PSCCalibration", "import BusyBeaver.ZFC.PowerSets", 1) == new_wf
    print("Exact declaration move and unchanged remaining proof bodies: PASS", flush=True)
    if not args.compile:
        return
    if not args.lean:
        parser.error("--compile requires --lean")
    lean = args.lean.resolve()
    version = subprocess.check_output([str(lean), "--version"], text=True).strip()
    if "4.32.0" not in version:
        raise ValueError(f"Expected Lean 4.32.0, got {version}")
    targets = ["BusyBeaver.ZFC.WFModelCore", "BusyBeaver.ZFC.PSCCalibration"]
    order = closure(targets, True)
    build = evidence / "build"
    build.mkdir(exist_ok=True)
    logdir = evidence / "logs"
    logdir.mkdir(exist_ok=True)
    records = []
    env = dict(os.environ, LEAN_PATH=str(build))
    for module in order:
        original, data, imports = source(module, True)
        if original is None:
            continue
        relative = Path(module.replace(".", "/"))
        dest = build / relative.with_suffix(".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        log = logdir / (module + ".log")
        argv = [str(lean), "-o", str(relative.with_suffix(".olean")), str(relative.with_suffix(".lean"))]
        started = time.perf_counter()
        proc = subprocess.run(argv, cwd=build, env=env, capture_output=True, text=True)
        elapsed = time.perf_counter() - started
        log.write_text(proc.stdout + proc.stderr)
        row = {"module": module, "source_sha256": sha256(data), "imports": imports,
               "exit_code": proc.returncode, "elapsed_seconds": elapsed,
               "log": str(log.relative_to(here)),
               "olean_sha256": sha256((build / relative.with_suffix(".olean")).read_bytes()) if proc.returncode == 0 else None}
        records.append(row)
        (evidence / "compile_records.json").write_text(json.dumps({"lean_version":version,"records":records}, indent=2)+"\n")
        print(f"{module}: exit {proc.returncode}, {elapsed:.3f}s", flush=True)
        if proc.returncode:
            print(proc.stdout + proc.stderr, flush=True)
            raise SystemExit(proc.returncode)
    audit_source = (here / "Audit.lean").read_text()
    (build / "Audit.lean").write_text(audit_source)
    audit = subprocess.run([str(lean), "-o", "Audit.olean", "Audit.lean"], cwd=build, env=env, capture_output=True, text=True)
    (evidence / "audit.log").write_text(audit.stdout + audit.stderr)
    (evidence / "result.json").write_text(json.dumps({"lean_version":version,"fresh_project_compilations":len(records),
        "all_project_exit_codes_zero":all(r["exit_code"]==0 for r in records),"audit_exit_code":audit.returncode,
        "endpoint_recompiled":False,"source_checks_passed":True}, indent=2)+"\n")
    print(audit.stdout + audit.stderr, flush=True)
    raise SystemExit(audit.returncode)


if __name__ == "__main__":
    main()
