#!/usr/bin/env python3
"""Read-only package verification, using only Python's standard library.

This checks exact finite algebra and integrity. It does not decide consistency
or replace the ordinary unbounded proofs and inherited logical calibration.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
FLAGS = ["-B"] + (["-O"] if sys.flags.optimize else [])


def require(ok, message):
    if not ok:
        raise ValueError(message)


def run(relative, *args):
    command = [sys.executable, *FLAGS, str(ROOT/relative), *map(str, args)]
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    require(completed.returncode == 0,
            relative+"\n"+completed.stdout+"\n"+completed.stderr)
    return json.loads(completed.stdout)


def manifest_check():
    path = ROOT/"MANIFEST.sha256.json"
    require(path.is_file(), "Package integrity manifest is missing.")
    manifest = json.loads(path.read_text())
    count = 0
    for relative, wanted in manifest["files"].items():
        target = (ROOT/relative).resolve()
        require(target.is_relative_to(ROOT), "Manifest path leaves the package: "+relative)
        require(target.is_file(), "Manifest file is missing: "+relative)
        require(hashlib.sha256(target.read_bytes()).hexdigest() == wanted,
                "Manifest mismatch: "+relative)
        count += 1
    return {"status": "PASS", "files": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path,
                        help="optionally write the complete result to this path")
    parser.add_argument("--rebuild-parent", action="store_true",
                        help="also rebuild the inherited common-remainder endpoint in a temporary directory")
    parser.add_argument("--skip-experiment", action="store_true")
    args = parser.parse_args()
    result = {
        "status": "PASS", "optimized_python": bool(sys.flags.optimize),
        "manifest": manifest_check(),
    }
    inherited_args = ["--rebuild"] if args.rebuild_parent else []
    inherited = run("source/inherited_common/code/verify.py", *inherited_args)
    require(inherited.get("status") == "PASS", "Inherited source verification failed.")
    source = run("source/verify_composed.py")
    require(source.get("status") == "PASS", "New source verification failed.")
    builder = run("code/build_final.py")
    require(builder.get("status") == "PASS", "Final reconstruction failed.")
    final = run("code/check_final.py")
    require(final.get("status") == "PASS", "Independent final audit failed.")
    result["inherited_common"] = inherited
    result["new_source"] = source
    result["reconstruction"] = builder
    result["final_independent_audit"] = final
    if not args.skip_experiment:
        result["separate_experiment"] = run(
            "experiments/three_parameter_calculus/verify_research.py")
    result["scope"] = (
        "Pinned inherited inputs, exact source delta, integral restoration, "
        "coordinate and row inverses, complete polynomial expansion, printed "
        "residuals, deliberate corruption controls, and optional finite experiment. "
        "Unbounded mathematical equivalence is proved in article.tex and the retained proofs."
    )
    payload = json.dumps(result, sort_keys=True, indent=2)+"\n"
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(payload)
    summary = {
        "status": "PASS", "optimized_python": result["optimized_python"],
        "manifest": result["manifest"],
        "metrics": final["metrics"],
        "source_corruptions_rejected": len(source["corruption_controls"]),
        "final_corruptions_rejected": len(final["corruption_controls"]),
        "experiment_checked": not args.skip_experiment,
        "receipt": str(args.receipt) if args.receipt else None,
    }
    print(json.dumps(summary, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
