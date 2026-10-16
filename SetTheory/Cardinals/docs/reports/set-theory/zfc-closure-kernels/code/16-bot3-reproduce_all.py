#!/usr/bin/env python3
"""Replay fixed mathematical-code and compiler checks; never search for a refutation."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import os


def main() -> int:
    if not __debug__:
        raise RuntimeError("Run without -O; the experiments retain assertion checks.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("reproduced"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = args.output_dir.resolve()
    if output == root or output in root.parents:
        parser.error("choose a dedicated result directory, not an ancestor of the package")
    output.mkdir(parents=True, exist_ok=True)
    py = sys.executable
    emitter = (root / "machine/proveit_snapshot/Computability/BusyBeaver/"
               "Research/ZFC/psc_backend_experiment.py")
    jobs = [
        ("checker_unit_tests",
         [py, "-m", "unittest", "-v", "test_psc_hilbert.py"],
         root / "reference_checker"),
        ("identity_certificate",
         [py, str(root / "reference_checker/psc_hilbert.py"),
          str(root / "reference_checker/identity.json")], root),
        ("bottom3_codec",
         [py, str(root / "code/bottom3_codec.py"), "--output",
          str(output / "bottom3-codec-results.json")], root),
        ("fixed_slot_obstruction",
         [py, str(root / "code/fixed_slot_obstruction.py"),
          "--emitter", str(emitter), "--output",
          str(output / "fixed-slot-obstruction-results.json")], root),
        ("independent_checker_review",
         [py, str(root / "code/review_psc_checker.py")], root),
        ("machine_fixed_replay",
         [py, str(root / "machine/reproduce.py"), "--output",
          str(output / "machine")], root),
    ]
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    results = []
    for name, command, directory in jobs:
        run = subprocess.run(command, cwd=directory, env=environment,
                             text=True, capture_output=True, check=False)
        (output / (name + ".stdout.txt")).write_text(run.stdout)
        (output / (name + ".stderr.txt")).write_text(run.stderr)
        results.append({"check": name, "exit_code": run.returncode,
                        "passed": run.returncode == 0})
        print(f"{name}: {'PASS' if run.returncode == 0 else 'FAIL'}", flush=True)
        if run.returncode:
            print(run.stdout)
            print(run.stderr)
            break
    summary = {
        "all_passed": len(results) == len(jobs) and all(r["passed"] for r in results),
        "checks": results,
        "python": sys.version.split()[0],
        "reference_checker_sha256": hashlib.sha256(
            (root / "reference_checker/psc_hilbert.py").read_bytes()).hexdigest(),
        "claims": {
            "finite_experiments_reproduced": True,
            "ZFC_consistency_proved": False,
            "sub254_machine_equivalence_proved": False,
            "unbounded_refutation_search_run": False,
            "Lean_or_Coq_build_run": False
        }
    }
    summary["claims"]["finite_experiments_reproduced"] = summary["all_passed"]
    (output / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Verification report: {output / 'verification.json'}")
    return 0 if summary["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
