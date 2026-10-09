#!/usr/bin/env python3
"""Import a completed, globally covering diameter-case run into the report.

Copy the immutable source, summary JSON, and full log into this package first.
This tool checks case coverage and records their provenance. It does not
independently prove the search program's UNSAT statements.
"""
from pathlib import Path
import argparse
import hashlib
import json

from verify_results import ROOT, check_case_coverage


def relative_file(name):
    path = (ROOT/name).resolve()
    if not path.is_relative_to(ROOT) or not path.is_file():
        raise ValueError("Inputs must be regular files within the research package.")
    return str(path.relative_to(ROOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True)
    parser.add_argument("--summary", required=True)
    parser.add_argument("--log", required=True)
    args = parser.parse_args()
    source, summary_file, log = map(
        relative_file, (args.source, args.summary, args.log)
    )
    summary = json.loads((ROOT/summary_file).read_text())
    assert summary["status"] == "UNSAT"
    allowed_scopes = {"all_diameter_cases"} | {
        f"all_top{depth}_diameter_cases" for depth in range(2, 7)
    }
    assert summary["scope"] in allowed_scopes
    assert summary["first_case"] == 0
    assert summary["last_case"]+1 == summary["case_count"]
    n, target = summary["n"], summary["target"]
    lower = max(
        (w["size"] for w in json.loads((ROOT/"data/witnesses.json").read_text())["witnesses"]
         if w["n"] == n), default=0
    )
    assert lower < target, "UNSAT claim conflicts with a verified witness."
    exact = lower == target-1
    record = {
        "n": n, "target_ruled_out": target,
        "derived_upper_bound": target-1,
        "derived_exact_value": lower if exact else None,
        "source_file": source,
        "source_sha256": hashlib.sha256((ROOT/source).read_bytes()).hexdigest(),
        "summary_file": summary_file,
        "log_file": log,
        "summary": summary,
        "method": "Exhaustive edge-prefix rainbow-clique search.",
        "qualification": "Case log is a computation record, not a formal UNSAT proof trace."
    }
    suffix = "exact" if exact else "upper"
    destination = ROOT/f"data/n{n}_{suffix}_certificate.json"
    destination.write_text(json.dumps(record, indent=2)+"\n")
    try:
        coverage = check_case_coverage(destination)
    except BaseException:
        destination.unlink()
        raise
    record["case_coverage_verified"] = True
    record["eligible_diameter_edges"] = coverage["eligible_edges"]
    record["diameter_orbits"] = coverage["covered_diameter_orbits"]
    destination.write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
