#!/usr/bin/env python3
"""Reproduce the finite checks and compare all measured outputs.

Uses only Python's standard library and the pinned vendor files. Candidate
checks are finite controls, not evidence for the consistency of EPSC2/ZFC.
No Lean/Coq build or end-to-end binary-compiler proof is claimed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def run(command, cwd):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    require(result.returncode == 0, result.stdout)
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path,
                        help="Optionally write a JSON summary to this path.")
    args = parser.parse_args()
    require(__debug__, "Run without -O or -OO; component checks use assertions.")

    provenance = json.loads((ROOT / "engineering/provenance.json").read_text())
    for source in provenance["sources"]:
        path = ROOT / "engineering" / source["path"]
        require(path.stat().st_size == source["bytes"],
                f"Vendor size mismatch: {source['path']}")
        require(sha256(path) == source["sha256"],
                f"Vendor hash mismatch: {source['path']}")
    print(f"Verified {len(provenance['sources'])} pinned source/notice hashes.")

    with tempfile.TemporaryDirectory(prefix="zfc-epsc2-reproduce-") as temporary:
        work = Path(temporary)
        checker = work / "checker"
        checker.mkdir()
        for name in ("epsc2_tableau.py", "test_epsc2_tableau.py"):
            shutil.copyfile(ROOT / "checker" / name, checker / name)
        run([sys.executable, "-B", "test_epsc2_tableau.py"], checker)
        observed_checker = json.loads(
            (checker / "epsc2_tableau_results.json").read_text())
        expected_checker = json.loads(
            (ROOT / "checker/epsc2_tableau_results.json").read_text())
        require(observed_checker == expected_checker,
                "Checker results differ from the supplied evidence.")
        print("Checker semantic, certificate, and codec controls match.")

        output = work / "engineering-results"
        run([sys.executable, "-B",
             str(ROOT / "engineering/compact_initializer.py"),
             "--output", str(output)], ROOT)
        observed_engineering = json.loads(
            (output / "compact-initializer-results.json").read_text())
        expected_engineering = json.loads(
            (ROOT / "engineering/results/compact-initializer-results.json")
            .read_text())
        require(observed_engineering == expected_engineering,
                "Initializer results differ from the supplied evidence.")
        machine_hashes = {}
        for label in ("zero", "nextproof2"):
            name = f"dag219-compact-{label}.tm"
            actual = output / name
            expected = ROOT / "engineering/results" / name
            require(actual.read_bytes() == expected.read_bytes(),
                    f"Transition-table byte mismatch: {name}")
            machine_hashes[name] = sha256(actual)
        print("Both regenerated transition tables and all engineering evidence match.")

    result = {
        "status": "passed",
        "source_cutoff": provenance["ProveIt_commit"],
        "vendor_hashes_checked": len(provenance["sources"]),
        "checker": observed_checker,
        "initializer_exact_replay_cases":
            observed_engineering["initializer_exact_replay_cases"],
        "parameter_minimization_cases":
            observed_engineering["parameter_minimization_cases"],
        "machine_hashes": machine_hashes,
        "complete_working_states": {
            label: data["working_states"]
            for label, data in observed_engineering["machine_variants"].items()
        },
        "same_layout_reproduction": True,
        "Lean_or_Coq_rebuilt": False,
        "new_literal_EPSC2_machine_delivered": False,
        "new_ZFC_consistency_state_bound_claimed": False,
    }
    if args.record:
        args.record.parent.mkdir(parents=True, exist_ok=True)
        args.record.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
