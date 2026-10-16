#!/usr/bin/env python3
"""Replay the finite evidence in this archive; never run an unbounded search."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def load(path):
    return json.loads(Path(path).read_text())


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled, without -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reproduced")
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    records = []

    def run(name, arguments, cwd=ROOT):
        print("Running " + name + "...", flush=True)
        completed = subprocess.run(
            [sys.executable, *map(str, arguments)], cwd=cwd,
            text=True, capture_output=True, check=False)
        (out / (name + ".log")).write_text(
            completed.stdout + completed.stderr)
        if completed.returncode:
            raise RuntimeError(
                name + " failed; inspect " + str(out / (name + ".log")))
        records.append({"name": name, "exit_code": completed.returncode})
        return completed.stdout

    run("qnand", [ROOT / "code/test_qnand.py",
                  "--output", out / "qnand_results.json"])
    if load(out / "qnand_results.json") != load(ROOT / "results/qnand_results.json"):
        raise RuntimeError("Main checker results differ from the delivered evidence.")

    run("independent_qnand", [ROOT / "code/audit_qnand.py",
                             "--output", out / "qnand_independent_results.json"])
    if load(out / "qnand_independent_results.json") != load(
            ROOT / "results/qnand_independent_results.json"):
        raise RuntimeError("Additional audit results differ from the delivered evidence.")

    # The examples use the generic signed-root checker, not public accepts().
    sys.path.insert(0, str(ROOT / "code"))
    import qnand as q
    example_results = []
    for example in load(ROOT / "examples/qnand_examples.json")["examples"]:
        arena = q.Arena()
        for expected_index, row in enumerate(example["arena"]):
            actual_index = arena.add(*row)
            if actual_index != expected_index:
                raise RuntimeError("Example arena indices are not canonical.")
        roots = [
            q.Entry(r["positive"], r["formula"], tuple(r["environment"]))
            for r in example["roots"]
        ]
        try:
            actual = q.check_tree(arena, roots, example["actions"])
        except q.Invalid as error:
            actual = {"valid": False, "reason": str(error)}
        if actual != example["result"]:
            raise RuntimeError("Example mismatch: " + example["name"])
        example_results.append({"name": example["name"], "result": actual})
    (out / "examples.json").write_text(json.dumps(example_results, indent=2) + "\n")
    records.append({"name": "exact_generic_examples", "matched": len(example_results)})

    control = ROOT / "machine_control"
    run("machine_control", [
        control / "library_grammar.py", "--output", out / "machine"
    ], cwd=control)
    if load(out / "machine/results.json") != load(control / "evidence/results.json"):
        raise RuntimeError("Fixed machine recipe differs from delivered evidence.")

    verification = run("independent_rm", [
        control / "vendor/verify_rm_certificate.py",
        "--source", control / "upstream/ZF/m254/coq/prog/Dag254.v",
        "--candidate", out / "machine/candidate_dag.json",
        "--certificate", out / "machine/rm_bisimulation.json",
    ], cwd=control)
    verification = json.loads(verification)
    (out / "independent_rm.json").write_text(
        json.dumps(verification, indent=2, sort_keys=True) + "\n")
    if not verification["verified"] or verification["pairs"] != 4533:
        raise RuntimeError("Independent register certificate did not verify.")
    wanted = load(control / "evidence/results.json")["total_table_sha256"]
    actual = digest(out / "machine/candidate_total.tm")
    if actual != wanted:
        raise RuntimeError("Total binary table digest differs from expected.")

    summary = {
        "status": "all finite replays passed",
        "python_version": sys.version.split()[0],
        "checks": records,
        "generic_examples": len(example_results),
        "working_states_in_separate_control": 269,
        "register_bisimulation_pairs": verification["pairs"],
        "total_control_table_sha256": actual,
        "reference_source_sha256": {
            str(p.relative_to(ROOT)): digest(p)
            for p in sorted((ROOT / "code").glob("*.py"))
        },
        "scope": (
            "Finite diagnostics and register correspondence only. "
            "No new binary compiler proof, consistency proof certificate, "
            "or quantified-NAND machine state bound."
        ),
    }
    (out / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
