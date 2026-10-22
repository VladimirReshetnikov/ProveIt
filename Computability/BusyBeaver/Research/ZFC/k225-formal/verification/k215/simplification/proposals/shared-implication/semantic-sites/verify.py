#!/usr/bin/env python3
"""Compile the isolated semantic-site refactoring; never edit the input repo."""
from __future__ import annotations
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

BASE = "2ca3a5c16f0876d2cab842056353c03a1ed2f5f0"
HERE = Path(__file__).resolve().parent

def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--build", type=Path, default=HERE / "build")
    args = ap.parse_args()
    repo = args.repo.resolve()
    source = repo / "Computability/BusyBeaver/Lean"
    build = args.build.resolve()
    baseline = build / "baseline"
    baseline.mkdir(parents=True, exist_ok=True)
    proposed = build / "proposed"
    proposed.mkdir(parents=True, exist_ok=True)
    lean = shutil.which(args.lean) if not Path(args.lean).is_absolute() else args.lean
    if not lean:
        raise SystemExit("Lean executable not found")
    version = subprocess.check_output([lean, "--version"], text=True).strip()
    head = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    if head != BASE:
        raise SystemExit(f"Expected checkout {BASE}; found {head}")
    seen: set[str] = set()
    order: list[str] = []
    imports: dict[str, list[str]] = {}
    source_hashes: dict[str, str] = {}
    def visit(module: str) -> None:
        if module in seen or module == "Init":
            return
        seen.add(module)
        rel = Path(*module.split(".")).with_suffix(".lean")
        original = source / rel
        if not original.is_file():
            raise SystemExit(f"Unexpected external import: {module}")
        content = original.read_bytes()
        source_hashes[str(rel)] = sha256(original)
        target = baseline / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
        imports[module] = []
        for line in content.decode().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    imports[module].append(dependency)
                    visit(dependency)
        order.append(module)
    visit("BusyBeaver.ZFC.KSim")
    shutil.copyfile(HERE / "audit/LegacySitesAudit.lean", baseline / "LegacySitesAudit.lean")
    records: list[dict] = []
    def compile_one(stage: str, work: Path, module: str) -> None:
        rel = Path(*module.split(".")).with_suffix(".lean")
        output = rel.with_suffix(".olean")
        command = [lean, "-j1", "-M12288", "-o", str(output), str(rel)]
        start = time.monotonic()
        cp = subprocess.run(command, cwd=work, env=dict(os.environ, LEAN_PATH=str(work)),
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - start
        log = work / (module.replace(".", "_") + ".log")
        log.write_text(cp.stdout)
        dependencies = {}
        for dep in imports.get(module, ["BusyBeaver.ZFC.KSim"]):
            path = work / Path(*dep.split(".")).with_suffix(".olean")
            if path.exists():
                dependencies[dep] = sha256(path)
        record = {"stage": stage, "module": module, "returncode": cp.returncode,
                  "seconds": round(elapsed, 3), "log": str(log.relative_to(build)),
                  "command": command, "cwd": str(work), "LEAN_PATH": str(work),
                  "compiled_source_sha256": sha256(work / rel),
                  "imports_olean_sha256": dependencies,
                  "olean_sha256": sha256(work / output) if cp.returncode == 0 else None}
        records.append(record)
        print(json.dumps(record), flush=True)
        if cp.returncode != 0:
            print(cp.stdout)
            raise RuntimeError(f"{stage}: {module} failed")
    passed = False
    try:
        with open("/tmp/proveit-k215-proof-build.lock", "w") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            for module in order + ["LegacySitesAudit"]:
                compile_one("baseline", baseline, module)
            # Reuse byte-identical dependencies only. Recompile changed provider and both clients.
            shutil.copytree(baseline / "BusyBeaver", proposed / "BusyBeaver", dirs_exist_ok=True)
            override = Path("BusyBeaver/ZFC/KSim.lean")
            shutil.copyfile(HERE / override, proposed / override)
            (proposed / override.with_suffix(".olean")).unlink(missing_ok=True)
            for audit in ["LegacySitesAudit", "SemanticSitesAudit"]:
                shutil.copyfile(HERE / f"audit/{audit}.lean", proposed / f"{audit}.lean")
            for module in ["BusyBeaver.ZFC.KSim", "LegacySitesAudit", "SemanticSitesAudit"]:
                compile_one("proposed", proposed, module)
            passed = True
    except RuntimeError as error:
        print(str(error))
    report = {"baseline": BASE, "lean_version": version,
              "project_modules": len(order), "records": records,
              "baseline_source_sha256": source_hashes,
              "legacy_audit_sha256": sha256(HERE / "audit/LegacySitesAudit.lean"),
              "semantic_audit_sha256": sha256(HERE / "audit/SemanticSitesAudit.lean"),
              "passed": passed}
    (build / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    return 0 if passed else 1

if __name__ == "__main__":
    raise SystemExit(main())
