#!/usr/bin/env python3
"""Check the proposed shared-residual patch in an isolated Lean overlay.

Invoke through the pinned repository's ``lake env``. This checks the four
proposed files, eight unchanged dependencies needed by their audit files,
and three existing audits. It does not modify the checkout or its outputs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--lean", default=shutil.which("lean") or "lean")
    ap.add_argument("--logs", type=Path, default=Path("replay-logs/residual-overlay"))
    args = ap.parse_args()
    repo = args.repo.resolve()
    here = Path(__file__).resolve().parent
    originals = repo / "Computability/DiophantineConsistency/Lean"
    bundle = here.parent
    logs = args.logs.resolve()
    logs.mkdir(parents=True, exist_ok=True)
    results = []
    patch_files = ["CompilerSupport", "DAGQuartic", "NaturalDAGQuartic", "QuadraticRegisterSystem"]
    order = ["CompilerSupport", "DAGQuartic", "NaturalDAGQuartic",
             "NaturalRegisterProgram", "NaturalRegisterRelation", "QuadraticRegisterSystem",
             "ComposeRepresentation", "PairingRepresentation", "RegisterRelationLogic",
             "QuadraticNatPairing", "QuadraticDivMod", "RegisterDivMod"]
    with tempfile.TemporaryDirectory(prefix="proveit-shared-residuals-") as temp:
        workspace = Path(temp)
        sources = workspace / "src"
        build = workspace / "build"
        (sources / "DiophantineConsistency").mkdir(parents=True)
        (build / "DiophantineConsistency").mkdir(parents=True)
        # Lean resolves a namespace directory from the first matching path.
        # Populate unchanged entries with read-only references; never link an
        # output that will be compiled, so this cannot overwrite the checkout.
        original_build = repo / ".lake/build/lib/lean/DiophantineConsistency"
        for item in original_build.iterdir():
            if item.name.split(".")[0] not in order:
                (build / "DiophantineConsistency" / item.name).symlink_to(item)
        for name in patch_files:
            shutil.copy2(bundle / "lean/overlay/DiophantineConsistency" / f"{name}.lean",
                         sources / "DiophantineConsistency" / f"{name}.lean")
        env = dict(os.environ)
        env["LEAN_PATH"] = str(build) + os.pathsep + env.get("LEAN_PATH", "")
        for name in order:
            source_root = sources if name in patch_files else originals
            source = source_root / "DiophantineConsistency" / f"{name}.lean"
            output = build / "DiophantineConsistency" / f"{name}.olean"
            command = [args.lean, "-j1", "-R", str(source_root), "-o", str(output), str(source)]
            log = logs / f"{name}.log"
            with log.open("w") as stream:
                proc = subprocess.run(command, cwd=repo, env=env, stdout=stream, stderr=subprocess.STDOUT)
            row = {"module": f"DiophantineConsistency.{name}", "exit_status": proc.returncode,
                   "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                   "source_kind": "patched" if name in patch_files else "unchanged dependency",
                   "log": str(log.relative_to(logs))}
            results.append(row)
            print(json.dumps(row), flush=True)
            if proc.returncode or "sorryAx" in log.read_text():
                break
        else:
            for name in ["DAGQuartic", "NaturalDAGQuartic", "QuadraticRegisterSystem"]:
                source = originals / "checks" / f"{name}.lean"
                log = logs / f"audit-{name}.log"
                with log.open("w") as stream:
                    proc = subprocess.run([args.lean, "-j1", str(source)], cwd=repo, env=env,
                                          stdout=stream, stderr=subprocess.STDOUT)
                row = {"audit": name, "exit_status": proc.returncode,
                       "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                       "log": str(log.relative_to(logs))}
                results.append(row)
                print(json.dumps(row), flush=True)
                if proc.returncode or "sorryAx" in log.read_text():
                    break
    success = len(results) == 15 and all(row["exit_status"] == 0 for row in results)
    success = success and all("sorryAx" not in (logs / row["log"]).read_text() for row in results)
    receipt = {"status": "PASS" if success else "FAIL", "results": results,
               "scope": "Four patched modules, eight unchanged audit dependencies, three existing audits; not a repository-wide rebuild"}
    (logs / "overlay-verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    raise SystemExit(0 if success else 1)


if __name__ == "__main__":
    main()
