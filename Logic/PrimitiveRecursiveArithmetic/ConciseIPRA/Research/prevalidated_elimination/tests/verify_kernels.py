"""Replay inherited certificates and controls for the sentinel refactoring.

All processes accept only with exit zero and exactly ACCEPT on stdout.
The intentionally unsound source mutation exists only in a temporary
directory; it is a guard-necessity control, not a candidate checker.
"""

import ast
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = ("checker.py", "checker_bytes.py", "checker_structure.py", "readable_checker.py")


def run(path, packet, optimized=False):
    proc = subprocess.run([sys.executable, *(["-O"] if optimized else []), str(path)],
                          input=json.dumps(packet), text=True, capture_output=True, timeout=20)
    return proc.returncode == 0 and proc.stdout.strip() == "ACCEPT"


def main():
    cases = json.loads((ROOT / "tests/cases.json").read_text())
    results = []
    for name in PROGRAMS:
        for optimized in (False, True):
            for case in cases:
                accepted = run(ROOT / "code" / name, case["packet"], optimized)
                results.append({"program": name, "optimized": optimized,
                                "case": case["name"], "expected": case["accept"],
                                "accepted": accepted, "passed": accepted == case["accept"]})

    # This closed goal is the false canonical equation 1=2.  Without
    # the non-real sentinel, a false-valued major with nonzero source
    # matches Python False and performs an unproved equality transport.
    sentinel_packet = json.loads((ROOT / "tests/reject_false_major_sentinel.json").read_text())
    controls = []
    for marker in (0, False, 0.0):
        packet = json.loads(json.dumps(sentinel_packet))
        packet[-2][0] = marker
        for name in PROGRAMS:
            for optimized in (False, True):
                accepted = run(ROOT / "code" / name, packet, optimized)
                controls.append({"program": name, "optimized": optimized,
                                 "marker": repr(marker), "accepted": accepted,
                                 "passed": not accepted})
    with tempfile.TemporaryDirectory() as tmp:
        mutant = Path(tmp) / "unsound_false_sentinel.py"
        source = (ROOT / "code/checker_bytes.py").read_text()
        source = source.replace("s and 1j or [t] * 3", "not s and [t] * 3")
        mutant.write_text(source)
        mutated_accepts_false = run(mutant, sentinel_packet)

    # Directly exercise the missing-image sentinel on our own opener;
    # omit only the driver's three final statements when loading it.
    tree = ast.parse((ROOT / "code/checker.py").read_text())
    namespace = {}
    exec(compile(ast.Module(body=tree.body[:-3], type_ignores=[]), "our_opener", "exec"), namespace)
    missing_image_rejected = False
    try:
        namespace["i"](3, d=3)
    except TypeError:
        missing_image_rejected = True
    controls_ok = all(row["passed"] for row in controls)
    result = {"inherited_cases": len(cases), "inherited_cli_runs": len(results),
              "inherited_accepts": sum(row["accepted"] for row in results),
              "inherited_rejects": sum(not row["accepted"] for row in results),
              "inherited_mismatches": [row for row in results if not row["passed"]],
              "sentinel_control_runs": len(controls), "sentinel_controls_passed": controls_ok,
              "unsafe_false_sentinel_mutation_accepts_1_equals_2": mutated_accepts_false,
              "missing_image_0j_rejected_with_TypeError": missing_image_rejected,
              "results": results, "sentinel_controls": controls}
    result["passed"] = (not result["inherited_mismatches"] and controls_ok
                        and mutated_accepts_false and missing_image_rejected)
    (ROOT / "evidence/verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ("results", "sentinel_controls")}, indent=2))
    if not result["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
