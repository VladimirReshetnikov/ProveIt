"""Run exact examples, compile the Lean sources and audit selected results."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
PURE = ["Oracle", "Zeros", "DyadicDetail", "LineDual"]
OBJECT = ["ReplayObject", "ZeroObject", "DyadicObject", "PrefixObject"]
EXAMPLES = ["zeros", "dyadic_derivative", "laws", "quantiles"]
AUDIT = {
    "Oracle": ["BoundedOracle.Reader.replay", "BoundedOracle.Reader.tableGuard_iff_uses",
               "BoundedOracle.Reader.read_sample", "BoundedOracle.WindowMap.thenMap",
               "BoundedOracle.respects_comp", "BoundedOracle.jump_no_window"],
    "Zeros": ["ConditionedZero.goodAt_unit", "ConditionedZero.width_run",
              "ConditionedZero.later_midpoints", "ConditionedZero.residual_unit"],
    "DyadicDetail": ["DyadicDetail.childFromSecondDifference", "DyadicDetail.secondDifferenceNoise",
                     "DyadicDetail.squareGridDetail"],
    "LineDual": ["LineDual.abel", "LineDual.optimal", "LineDual.dual_attained",
                 "LineDual.dual_upper", "LineDual.Scaled.edge_certificate", "LineDual.Scaled.abel_step"],
    "ReplayObject": ["Observation.ReplayObject.replay", "Observation.ReplayObject.sparse_replay"],
    "ZeroObject": ["Observation.ZeroObject.branches_closed"],
    "DyadicObject": ["Observation.DyadicObject.child_from_adjacent_closed"],
    "PrefixObject": ["Observation.PrefixObject.prefix_upper", "Observation.PrefixObject.covers_latest",
                     "Observation.PrefixObject.increasing"]
}


def command(args, cwd, env=None):
    proc = subprocess.run(args, cwd=cwd, env=env, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return proc.stdout


def provider_check(repo):
    paths = json.loads((ROOT / "verification/provider-hashes.json").read_text())
    for name, expected in paths.items():
        family = "Derivations" if name.startswith("IPRADerivations.") else "ConciseIPRA"
        path = repo/"Logic/PrimitiveRecursiveArithmetic"/family/"Lean"/(name.replace(".", "/")+".lean")
        raw = path.read_bytes()
        sha = hashlib.sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()
        if sha != expected:
            raise SystemExit(f"Provider differs from the verified source: {path}")
    print(f"Matched {len(paths)} ProveIt provider source blobs.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--proveit", type=Path, help="root of a configured ProveIt checkout")
    target.add_argument("--object-env", action="store_true", help="use existing Lean provider paths in LEAN_PATH")
    target.add_argument("--standalone", action="store_true", help="run examples and four standalone modules")
    target.add_argument("--examples-only", action="store_true", help="run the Python examples only")
    parser.add_argument("--lean", default="lean", help="Lean executable outside --proveit mode")
    args = parser.parse_args()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for example in EXAMPLES:
        print(f"\n{example}.py", flush=True)
        print(command([sys.executable, str(ROOT/"examples"/(example+".py"))], ROOT, env).rstrip())
    if args.examples_only:
        return
    if args.proveit:
        repo = args.proveit.resolve()
        provider_check(repo)
        subprocess.run(["lake", "build", "+IPRADerivations.Core.BoundedSums"], cwd=repo, check=True)
        executable = command(["lake", "env", "which", "lean"], repo).strip()
        raw_path = command(["lake", "env", "printenv", "LEAN_PATH"], repo).strip()
        search = [str((repo/entry).resolve()) for entry in raw_path.split(os.pathsep) if entry]
    else:
        executable = shutil.which(args.lean)
        if not executable:
            raise SystemExit("Provide Lean 4.32.0 using --lean or put it on PATH.")
        search = os.environ.get("LEAN_PATH", "").split(os.pathsep) if args.object_env else []
    print("\n" + command([executable, "--version"], ROOT).strip())
    modules = PURE if args.standalone else PURE + OBJECT
    with tempfile.TemporaryDirectory() as directory:
        out = Path(directory)
        env["LEAN_PATH"] = os.pathsep.join([str(out)] + [s for s in search if s])
        for module in modules:
            print("Checking " + module, flush=True)
            print(command([executable, "-o", str(out/(module+".olean")), module+".lean"],
                          ROOT/"lean", env).strip())
        audit = out/"Audit.lean"
        lines = ["import " + mod for mod in modules]
        lines += ["#print axioms " + thm for mod in modules for thm in AUDIT[mod]]
        audit.write_text("\n".join(lines)+"\n")
        log = command([executable, audit.name], out, env)
        print("\n" + log.strip())
        if "sorryAx" in log:
            raise SystemExit("An audited declaration depends on sorryAx.")
    print(f"\nAll {len(modules)} Lean modules and {len(EXAMPLES)} exact examples passed.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as exc:
        if exc.stdout:
            print(exc.stdout, file=sys.stderr)
        raise
