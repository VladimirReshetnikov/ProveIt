#!/usr/bin/env python3
"""Compile only this packet's modules using a pinned, prebuilt ProveIt checkout.

The checkout's source is read-only.  This script never installs Lean, clones a
repository, updates a dependency, or builds an upstream module.  Required
upstream .olean files must already exist.  Outputs and logs go to --output.
"""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

EXPECTED_SHA = "bbb85238dac533fc4b7b84a750cca864fe35fed5"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
MODULES = ["EuclideanIPRA/Derivations", "EuclideanIPRA/GeometrySyntax", "EuclideanIPRA"]


def read_command(args: list[str], cwd: Path) -> str:
    p = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if p.returncode:
        raise RuntimeError(f"Command failed: {args!r}\n{p.stdout}{p.stderr}")
    return p.stdout.strip()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", required=True, type=Path, help="Pinned ProveIt checkout")
    p.add_argument("--output", type=Path, default=Path(__file__).parent / "build")
    args = p.parse_args()
    repo = args.repo.resolve(strict=True)
    source = Path(__file__).parent.resolve()
    out = args.output.resolve()
    if out == repo or repo in out.parents or out in repo.parents:
        raise SystemExit("Choose an output directory disjoint from the upstream checkout, not its ancestor.")
    # Resolve every planned destination before writing. Existing symlinks in
    # an otherwise disjoint output tree must not redirect writes upstream.
    destinations = [out / "src", out / "lib", out / "build.log", out / "result.json"]
    for module in MODULES:
        destinations.extend([out / "src" / (module + ".lean"),
                             out / "lib" / (module + ".olean")])
    for destination in destinations:
        actual = destination.resolve()
        if actual == repo or repo in actual.parents or actual in repo.parents:
            raise SystemExit("An output destination overlaps the upstream checkout: " + str(destination))
    sha = read_command(["git", "rev-parse", "HEAD"], repo)
    if sha != EXPECTED_SHA:
        raise SystemExit(f"Expected upstream commit {EXPECTED_SHA}; found {sha}.")
    toolchain = (repo / "lean-toolchain").read_text().strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise SystemExit(f"Unexpected toolchain: {toolchain}")
    protected = ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
                 "Logic/PrimitiveRecursiveArithmetic/ConciseIPRA",
                 "Logic/PrimitiveRecursiveArithmetic/Derivations"]
    dirty = subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *protected], cwd=repo)
    if dirty.returncode:
        raise SystemExit("The relevant upstream source differs from the pinned commit.")
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("Lake is unavailable. Install the pinned toolchain before running this script.")
    required = ["IPRADerivations/Core/Tactic.olean",
                "IPRADerivations/Core/IntCertificates.olean",
                "IPRADerivations/Core/Definitions.olean"]
    root_lib = repo / ".lake/build/lib/lean"
    missing = [x for x in required if not (root_lib / x).is_file()]
    if missing:
        raise SystemExit("Upstream modules are not prebuilt: " + ", ".join(missing)
            + "\nIn the checkout, first run: lake build IPRADerivations.Core.IntCertificates "
            "IPRADerivations.Core.Definitions")
    lean = read_command([lake, "env", "which", "lean"], repo)
    # Read only the public runtime path variables needed by Lean; never dump
    # the complete environment, which can contain unrelated credentials.
    runtime_keys = ["LEAN_PATH", "LD_LIBRARY_PATH", "DYLD_LIBRARY_PATH"]
    runtime_code = "import os,json; print(json.dumps({k:os.environ.get(k,'') for k in " + repr(runtime_keys) + "}))"
    runtime_paths = json.loads(read_command([lake, "env", sys.executable, "-c", runtime_code], repo))
    lib = out / "lib"
    src = out / "src"
    lib.mkdir(parents=True, exist_ok=True)
    src.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    for key, value in runtime_paths.items():
        # Lake may report relative search paths. The compiler will run in the
        # isolated source directory, so resolve them against the checkout.
        paths = []
        for item in value.split(os.pathsep):
            if item:
                path = Path(item)
                paths.append(str(path if path.is_absolute() else (repo / path).resolve()))
        if paths:
            env[key] = os.pathsep.join(paths)
    env["LEAN_PATH"] = str(lib) + os.pathsep + env.get("LEAN_PATH", "")
    version = read_command([lean, "--version"], repo)
    if "4.32.0" not in version:
        raise SystemExit(f"Unexpected Lean version: {version}")
    completed = []
    log = [f"upstream={sha}", f"compiler={version}"]
    for module in MODULES:
        target = src / (module + ".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source / (module + ".lean"), target)
        compiled = lib / (module + ".olean")
        compiled.parent.mkdir(parents=True, exist_ok=True)
        cmd = [lean, module + ".lean", "-o", str(compiled)]
        run = subprocess.run(cmd, cwd=src, env=env, capture_output=True, text=True)
        log.extend([" ".join(cmd), run.stdout, run.stderr])
        (out / "build.log").write_text("\n".join(log), encoding="utf-8")
        if run.returncode:
            (out / "result.json").write_text(json.dumps({
                "compiled": False, "completed": completed, "failed_module": module,
                "upstream_commit": sha, "compiler": version}, indent=2) + "\n")
            raise SystemExit(f"Compilation failed for {module}; see {out / 'build.log'}")
        completed.append(module)
    (out / "result.json").write_text(json.dumps({
        "compiled": True, "completed": completed,
        "upstream_commit": sha, "compiler": version,
        "full_algebraic_backend": False,
        "full_theorem_portfolio": False}, indent=2) + "\n")
    print(f"Compiled {len(completed)} packet modules. Log: {out / 'build.log'}")


if __name__ == "__main__":
    main()
