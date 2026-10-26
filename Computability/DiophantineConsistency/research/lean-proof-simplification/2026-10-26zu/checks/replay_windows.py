#!/usr/bin/env python3
"""Check the helper and generic post-y pairing kernel using a configured repo.

The checkout must already have Lean 4.32.0 and its pinned Mathlib dependencies
available. No source file in that checkout is changed; temporary objects are
removed on exit. This does not rebuild the internal-natural wrapper.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import tempfile

PACKET = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True,
                        help="Configured ProveIt checkout with dependencies")
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    repo = args.repo.resolve()
    environment_probe = (
        "import json, os, shutil; "
        "print(json.dumps({'lean': shutil.which('lean'), "
        "'env': dict(os.environ)}))"
    )
    probe = subprocess.run(
        [args.lake, "env", sys.executable, "-c", environment_probe], cwd=repo,
        text=True, capture_output=True, check=True,
    )
    config = json.loads(probe.stdout)
    lean, env = config["lean"], config["env"]
    if not lean:
        raise SystemExit("lake env could not locate Lean")
    version = subprocess.run([lean, "--version"], cwd=repo, env=env,
                             text=True, capture_output=True, check=True).stdout.strip()
    if "version 4.32.0" not in version:
        raise SystemExit(f"Expected Lean 4.32.0; found {version}")
    print(version, flush=True)
    with tempfile.TemporaryDirectory(prefix="proveit-windows-") as directory:
        lib = Path(directory)
        output = lib / "DiophantineConsistency" / "OrderedWindow.olean"
        output.parent.mkdir(parents=True)
        env["LEAN_PATH"] = str(lib) + os.pathsep + env.get("LEAN_PATH", "")
        helper = PACKET / "windows/lean/DiophantineConsistency/OrderedWindow.lean"
        kernel = PACKET / "windows/kernels/PairingKernel.lean"
        subprocess.run([lean, "-o", str(output), str(helper)], cwd=repo,
                       env=env, check=True)
        subprocess.run([lean, str(kernel)], cwd=repo, env=env, check=True)
    print("PASS: complete helper and generic post-y pairing namespace.")
    print("The internal-natural wrapper and full repository were not rebuilt.")


if __name__ == "__main__":
    main()
