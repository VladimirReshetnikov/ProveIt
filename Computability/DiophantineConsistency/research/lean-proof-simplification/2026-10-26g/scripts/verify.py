#!/usr/bin/env python3
"""Replay the delivered Lean experiments without editing the repository.

Usage: python3 scripts/verify.py --repo /path/to/ProveIt [--full]
Requires Python 3.10+, git, the pinned Lean/Lake toolchain, and mathlib dependencies.
The default checks the eight core experiments and the complete Representation patch.
--full additionally checks any delivered current-equation adapters listed below.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

COMMIT = "60e9c5d620c6c387d932876cfa2d9376f64ea56c"
MATHLIB = "81a5d257c8e410db227a6665ed08f64fea08e997"
REP = "Computability/DiophantineConsistency/Lean/DiophantineConsistency/Representation.lean"
ORIGINAL_SHA = "69427aad8d135be6c680643ab073b11cd9f74683f1ba1fa5a116fb346fcac136"
CORE = [
    "GenericScanner", "HalfRadixCore", "OneHotCore", "CarryCore",
    "CyclicFieldRefactor", "AssignmentTransport", "DAGRefactoring", "HalfRadixRefactor",
]
EXTRA_TARGETS = {
    "PositiveZeroRefactor": ["DiophantineConsistency.CurrentCarrierArithmetic2011"],
    "ReflectedResidueRefactor": ["DiophantineConsistency.CurrentClause2011"],
    "WordOriginRefactor": ["DiophantineConsistency.NativeRadixDigits"],
    "CyclicFieldProjectAdapter": ["DiophantineConsistency.CurrentClause2011"],
}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo", required=True, type=Path)
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--output", type=Path, help="Fresh replay directory (default: bundle/replay)")
    args = ap.parse_args()
    bundle = Path(__file__).resolve().parents[1]
    repo = args.repo.resolve()
    out = (args.output or bundle / "replay").resolve()
    if out.exists():
        raise SystemExit(f"Replay output already exists: {out}; choose a new --output directory.")
    out.mkdir(parents=True)
    logs = out / "logs"
    logs.mkdir()
    receipts: list[dict] = []

    def capture(argv: list[str]) -> str:
        return subprocess.check_output(argv, cwd=repo, text=True).strip()

    def run(argv: list[str], label: str, env: dict | None = None) -> None:
        log = logs / (label + ".log")
        print(f"Checking {label} ...", flush=True)
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(argv, cwd=repo, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT, text=True)
        receipt = {"label": label, "command": argv, "exit_code": result.returncode,
                   "log": str(log.relative_to(out)),
                   "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
        if argv[-1].endswith(".lean") and Path(argv[-1]).is_file():
            receipt["source"] = argv[-1]
            receipt["source_sha256"] = hashlib.sha256(Path(argv[-1]).read_bytes()).hexdigest()
            output = log.read_text(encoding="utf-8")
            audits = {}
            for name, text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output):
                audits[name] = [x.strip() for x in text.split(",") if x.strip()]
            for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
                audits[name] = []
            receipt["axiom_audits"] = audits
            unexpected = set(a for xs in audits.values() for a in xs) - {
                "propext", "Classical.choice", "Quot.sound"}
            if unexpected:
                raise SystemExit(f"Unexpected axiom dependencies in {label}: {unexpected}")
        receipts.append(receipt)
        (out / "status.json").write_text(json.dumps({"commit": COMMIT, "mathlib_commit": MATHLIB,
                                                   "scope": "Selected experiments and patched module; no whole-repository rebuild",
                                                   "checks": receipts},
                                                   indent=2) + "\n", encoding="utf-8")
        if result.returncode:
            raise SystemExit(f"Check failed; see {log}")

    if capture(["git", "rev-parse", "HEAD"]) != COMMIT:
        raise SystemExit("Use a checkout at the exact commit documented in the report.")
    if (repo / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.32.0":
        raise SystemExit("The repository's lean-toolchain file differs from the reviewed snapshot.")
    manifest = json.loads((repo / "lake-manifest.json").read_text())
    if next(p["rev"] for p in manifest["packages"] if p["name"] == "mathlib") != MATHLIB:
        raise SystemExit("The mathlib pin differs from the reviewed snapshot.")
    run(["git", "diff", "--exit-code", COMMIT, "--",
         "Computability/DiophantineConsistency/Lean", "Computability/HilbertTenthProblem/Lean",
         "Computability/BusyBeaver/Lean", "SetTheory/ZF/Lean", "Logic/FirstOrder/Lean"],
        "source-unchanged")
    run(["lake", "env", "lean", "--version"], "compiler-version")

    modules = CORE.copy()
    targets = ["DiophantineConsistency.ArithmeticDAGDegree",
               "DiophantineConsistency.ArithmeticDAGPowers",
               "DiophantineConsistency.NativeCyclicRotation"]
    if args.full:
        for name, needed in EXTRA_TARGETS.items():
            if (bundle / "lean" / (name + ".lean")).is_file():
                modules.append(name)
                targets.extend(needed)
    run(["lake", "build", *dict.fromkeys(targets)], "repository-dependencies")

    # Get Lake's configured search path without dumping any unrelated environment.
    lake_path = capture(["lake", "env", sys.executable, "-c",
                         "import os; print(os.environ.get('LEAN_PATH', ''))"])
    original_root = out / "original-source"
    original_source = original_root / "DiophantineConsistency" / "Representation.lean"
    original_source.parent.mkdir(parents=True)
    original_bytes = subprocess.check_output(["git", "show", COMMIT + ":" + REP], cwd=repo)
    if hashlib.sha256(original_bytes).hexdigest() != ORIGINAL_SHA:
        raise SystemExit("Pinned original source hash mismatch.")
    original_source.write_bytes(original_bytes)
    original_lib = out / "original-lib"
    original_olean = original_lib / "DiophantineConsistency" / "Representation.olean"
    original_olean.parent.mkdir(parents=True)
    run(["lake", "env", "lean", "--root=" + str(original_root), "-o",
         str(original_olean), str(original_source)], "original-Representation")

    # The unchanged original precedes other roots only for the compatibility
    # module. Lean resolves a namespace directory in the first matching root;
    # leaving this partial directory first would shadow unrelated project modules.
    proto_lib = out / "prototype-lib"
    proto_lib.mkdir()
    env = os.environ.copy()
    for module in modules:
        source = bundle / "lean" / (module + ".lean")
        roots = [str(proto_lib), lake_path]
        if module == "AssignmentTransport":
            roots.insert(0, str(original_lib))
        env["LEAN_PATH"] = os.pathsep.join(roots)
        # lake env resets LEAN_PATH, so invoke its selected Lean executable directly.
        lean = capture(["lake", "env", sys.executable, "-c",
                        "import shutil; print(shutil.which('lean'))"])
        run([lean, "--root=" + str(bundle / "lean"), "-o",
             str(proto_lib / (module + ".olean")), str(source)], module, env)

    patch = bundle / "patches" / "Representation-refactor.patch"
    run(["git", "apply", "--check", str(patch)], "patch-applicability")
    patched_root = bundle / "refactored-source"
    patched = patched_root / "DiophantineConsistency" / "Representation.lean"
    # A separate output path prevents the patched module from shadowing the original above.
    run(["lake", "env", "lean", "--root=" + str(patched_root), "-o",
         str(out / "RepresentationRefactored.olean"), str(patched)], "patched-Representation")
    print(f"All requested checks passed. Receipts: {out / 'status.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
