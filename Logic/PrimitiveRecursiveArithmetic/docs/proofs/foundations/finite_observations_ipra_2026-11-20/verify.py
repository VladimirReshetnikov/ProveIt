#!/usr/bin/env python3
"""Replay examples and, optionally, the Lean modules with their required providers."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
HOST = ("ModelCase", "TopologyCase", "ComplexCase")
OBJECT = ("MetricKernel", "ModelObject", "TopologyObject", "ComplexObject", "UniformMinimum")
REV = "5f3be02388442f16487d2dc5c2529961dd783d2b"


def run(cmd, **kwargs):
    print("+", " ".join(str(x) for x in cmd), flush=True)
    subprocess.run(cmd, check=True, **kwargs)


def lean_check(compiler, providers, modules):
    with tempfile.TemporaryDirectory(prefix="ipra-observations-") as build:
        env = {**os.environ, "LEAN_PATH": os.pathsep.join([build, *providers])}
        run([compiler, "--version"])
        for mod in modules:
            run([compiler, "-R", ROOT / "lean", "-o", Path(build) / (mod + ".olean"),
                 ROOT / "lean" / (mod + ".lean")], env=env, cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--host-lean", action="store_true", help="also replay the core-only modules")
    mode.add_argument("--proveit", type=Path, help="build providers in a ProveIt checkout and replay every module")
    mode.add_argument("--providers", help="use a prepared Lean search path and replay every module")
    parser.add_argument("--lean", default="lean", help="compiler for --host-lean or --providers")
    args = parser.parse_args()

    for example in sorted((ROOT / "examples").glob("*.py")):
        run([sys.executable, example])
    if args.proveit:
        repo = args.proveit.resolve()
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        print("ProveIt revision:", head, "(report uses", REV + ")", flush=True)
        lake = shutil.which("lake")
        if not lake:
            parser.error("lake is required in PATH for --proveit")
        run([lake, "build", "+IPRADerivations.Core.Order:olean"], cwd=repo)
        provided = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=repo,
                                           text=True).strip().split(os.pathsep)
        # Lake may emit relative package build directories.
        paths = [str((repo / p).resolve()) for p in provided if p]
        prefix = subprocess.check_output([lake, "env", "lean", "--print-prefix"], cwd=repo, text=True).strip()
        compiler = Path(prefix) / "bin" / "lean"
        lean_check(compiler, paths, (*HOST, *OBJECT))
    elif args.providers:
        lean_check(args.lean, args.providers.split(os.pathsep), (*HOST, *OBJECT))
    elif args.host_lean:
        lean_check(args.lean, [], HOST)


if __name__ == "__main__":
    main()
