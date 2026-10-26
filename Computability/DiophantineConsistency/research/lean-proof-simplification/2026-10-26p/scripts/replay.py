#!/usr/bin/env python3
"""Explicit, targeted replay in a caller-supplied clean checkout."""
from pathlib import Path
import argparse
import subprocess
import sys
root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument("--repo", type=Path, required=True)
p.add_argument("--apply", action="store_true", help="Apply the four patches to the supplied checkout")
p.add_argument("--build", action="store_true", help="After applying, build targeted modules and run audits")
a = p.parse_args()
repo = a.repo.resolve()
if a.build and not a.apply:
    p.error("--build requires --apply; use a fresh checkout for this replay")
def git(*args):
    return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()
commit = git("rev-parse", "HEAD")
allowed = {"7fa06d530df54d4aeb2e18027409df082234c69e", "6f46a5e3480a2fa2e45993b8090826f256aeaa56"}
if commit not in allowed:
    sys.exit("Use one of the two recorded commits; review newer changes separately.")
if git("status", "--porcelain", "--untracked-files=no"):
    sys.exit("The supplied checkout has tracked changes. Use a fresh checkout.")
patches = sorted((root / "patches").glob("*.patch"))
subprocess.run(["git", "apply", "--check", *map(str, patches)], cwd=repo, check=True)
print("All four patches apply at", commit, flush=True)
if not a.apply:
    sys.exit(0)
subprocess.run(["git", "apply", *map(str, patches)], cwd=repo, check=True)
if not a.build:
    sys.exit(0)
logs = root / "replay-output"
logs.mkdir(exist_ok=True)
def run(name, command):
    print("Running", name, flush=True)
    with (logs / (name + ".log")).open("w") as stream:
        result = subprocess.run(command, cwd=repo, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        sys.exit(f"{name} failed; see {logs / (name + '.log')}")
run("targeted-build", ["lake", "build", "+DiophantineConsistency.NativeHalfBinomial", "+DiophantineConsistency.AnnotatedProofChecker", "+DiophantineConsistency.AnnotatedSyntaxGraphs", "+DiophantineConsistency.NativeTemporalSupport54"])
for file in sorted((root / "audits").glob("*.lean")):
    run(file.stem, ["lake", "env", "lean", str(file)])
file = root / "prototypes/CanonicalPairingIntegration.lean"
run(file.stem, ["lake", "env", "lean", str(file)])
print("Targeted replay completed. This does not rebuild the complete umbrella.")
