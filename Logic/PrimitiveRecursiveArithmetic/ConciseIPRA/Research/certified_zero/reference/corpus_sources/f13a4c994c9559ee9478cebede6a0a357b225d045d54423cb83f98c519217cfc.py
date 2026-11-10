"""Reproduce the complete-checker comparison and the supplied evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FIELDS = ("normalized_tokens", "ast_nodes", "normalized_bytes")


def main():
    receipts = []
    for name in ("tests/reproduce_arithmetic.py", "code/test_checker.py",
                 "code/test_matched.py", "tests/audit_substitution.py",
                 "compact_controls/replay.py"):
        run = subprocess.run([sys.executable, str(ROOT / name)], cwd=ROOT,
                             text=True, capture_output=True, timeout=120)
        if run.returncode:
            raise RuntimeError(name + " failed:\n" + run.stdout + run.stderr)
        receipts.append({"script": name, "exit_code": run.returncode})
        print(name + ": PASS", flush=True)
    spec = importlib.util.spec_from_file_location("source_measure", ROOT / "comparison/source_measure.py")
    meter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(meter)
    provenance = json.loads((ROOT / "comparison/provenance.json").read_text())
    for entry in provenance:
        actual = hashlib.sha256((ROOT / "comparison" / entry["file"]).read_bytes()).hexdigest()
        if actual != entry["sha256"]:
            raise ValueError("Changed frozen comparator: " + entry["file"])
    rows = []
    for name in ("comparison/old_tokens.py", "comparison/old_structure.py",
                 "comparison/old_bytes.py", "code/checker_four_schema.py", "code/checker.py"):
        rows.append({"file": name, **meter.metrics(ROOT / name)})
    old, new = rows[-2:]
    reductions = {field: old[field] - new[field] for field in FIELDS}
    if not all(value > 0 for value in reductions.values()):
        raise ValueError("Matched strict reduction did not reproduce on this runtime")
    controls = []
    for index, profile in enumerate(("tokens", "structure", "bytes")):
        name = "compact_controls/" + profile + ".py"
        row = {"file": name, **meter.metrics(ROOT / name)}
        if not all(row[f] < rows[index][f] for f in FIELDS):
            raise ValueError("Composed control did not improve its original: " + profile)
        controls.append(row)
    result = {
        "python": platform.python_version(), "implementation": platform.python_implementation(),
        "status": "passed", "scripts": receipts, "complete_source_measurements": rows,
        "included_prior_coordinate_minima": {f: min(row[f] for row in rows[:3]) for f in FIELDS},
        "matched_reductions": reductions,
        "new_gj_global_frontier_improvement": False,
        "new_gj_checker_below_prior_coordinate_envelope": False,
        "composed_inherited_control_measurements": controls,
        "composed_inherited_coordinate_minima": {f: min(row[f] for row in controls) for f in FIELDS},
        "single_composed_control_below_all_prior_minima": any(
            all(row[f] < min(old_row[f] for old_row in rows[:3]) for f in FIELDS)
            for row in controls),
        "scope": "Complete-source comparison and finite evidence; universal claims use written proofs."
    }
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in ("scripts", "complete_source_measurements")}, indent=2))


if __name__ == "__main__":
    main()
