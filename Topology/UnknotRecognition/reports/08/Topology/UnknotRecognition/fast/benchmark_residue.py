"""Reproduce intrinsic prefix profiles on actual scanning complexes.

Run from fast/: python3 benchmark_residue.py --output results/residue_profiles.json
This records deterministic work and equality checks, not performance claims
about running the diagnostic inside the recognition pipeline.
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path

from fastunknot.diagram import Diagram
from fastunknot.ordering import best_scan_order
from fastunknot.residue import object_profile, residue_profile, profile_records
from fastunknot.scan import ScanComplex
from fastunknot.scan_fast import FastScan


def measure(name, diagram):
    order = best_scan_order(diagram.pd)
    configurations = [
        ("optimized", lambda: FastScan()),
        ("generic_minfill", lambda: ScanComplex(pivot="minfill")),
        ("generic_lifo", lambda: ScanComplex(pivot="lifo")),
        ("sets_lifo", lambda: ScanComplex(pivot="lifo", algebra="sets")),
    ]
    rows = []
    expected_profiles = None
    for label, constructor in configurations:
        scanner = constructor()
        stages = []
        profiles = []
        for stage, crossing in enumerate(order, 1):
            scanner.add_crossing(diagram.pd[crossing], reduce_now=False)
            before = sum(object_profile(scanner).values())
            predicted = residue_profile(scanner, check_squared=True)
            scanner.eliminate()
            actual = object_profile(scanner)
            assert predicted == actual, (name, label, stage)
            profiles.append(profile_records(actual))
            stages.append({
                "stage": stage, "crossing": crossing,
                "boundary_points": len(scanner.points),
                "objects_before": before,
                "canonical_objects_after": sum(actual.values()),
                "matching_types_after": len({matching for matching, degree in actual}),
                "profile": profiles[-1],
            })
        if expected_profiles is None:
            expected_profiles = profiles
        else:
            assert profiles == expected_profiles, (name, label)
        rows.append({
            "configuration": label, "stages": stages,
            "peak_objects_before": max(s["objects_before"] for s in stages),
            "peak_canonical_objects": max(s["canonical_objects_after"] for s in stages),
            "peak_boundary_points": max(s["boundary_points"] for s in stages),
            "final_unreduced_rank": stages[-1]["canonical_objects_after"],
            "stats": scanner.stats,
        })
    return {"name": name, "pd": [list(row) for row in diagram.pd],
            "crossings": diagram.crossings, "order": order, "runs": rows,
            "all_predictions_match": True, "all_completed_profiles_match": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="results/residue_profiles.json")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    names = ["conway", "kinoshita_terasaka", "figure_eight", "hard_unknot_8", "torus_3_5"]
    examples = [(name, Diagram.from_json(json.loads(
        (root / "examples" / (name + ".json")).read_text()))) for name in names]
    examples.append(("alternating_3braid_10", Diagram.from_braid(3, [1, -2] * 5)))
    cases = [measure(name, diagram) for name, diagram in examples]
    result = {
        "python": platform.python_version(), "platform": platform.platform(),
        "field": "F2", "degree_convention": "unnormalized cube degree",
        "cases": cases,
        "prefixes_per_configuration": sum(case["crossings"] for case in cases),
        "pre_post_checks": 4 * sum(case["crossings"] for case in cases),
        "all_checks_passed": True,
    }
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in
                      ("prefixes_per_configuration", "pre_post_checks", "all_checks_passed")}))
    for case in cases:
        print(case["name"], [(r["configuration"], r["peak_canonical_objects"],
                             r["stats"]["compositions"]) for r in case["runs"]])


if __name__ == "__main__":
    main()
