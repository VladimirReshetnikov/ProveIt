"""Focused byte-selector checks, with the intentional alias difference."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
manifest = json.loads((root / "fixtures/manifest.json").read_text())
cases = []
for item in manifest["cases"]:
    if item["path"].startswith("fixtures/zero/"):
        cases.append((item["name"], root / item["path"],
                      [item["expected"], item["expected"]]))
manual = json.loads((root / "fixtures/byte_arity/expected.json").read_text())
for name, expected in manual.items():
    cases.append((name, root / "fixtures/byte_arity" / (name + ".json"), expected))
programs = [root / "reference/checkers/bytes.py", root / "checkers/bytes.py"]
receipts = []
failures = []
for name, fixture, expected in cases:
    data = fixture.read_bytes()
    for optimized in [False, True]:
        actual = []
        for program in programs:
            command = [sys.executable] + (["-O"] if optimized else []) + [str(program)]
            result = subprocess.run(command, input=data, capture_output=True, timeout=20)
            actual.append(result.returncode == 0 and result.stdout == b"ACCEPT\n")
        row = {"name": name, "optimized": optimized,
               "expected_control_candidate": expected,
               "actual_control_candidate": actual}
        receipts.append(row)
        if actual != expected:
            failures.append(row)
report = {"fixture_cases": len(cases), "paired_runs": len(receipts),
          "process_executions": 2 * len(receipts),
          "intentional_difference": "empty_truth_alias: control accepts; candidate rejects",
          "failures": failures, "results": receipts}
(root / "evidence/byte_validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
if failures:
    raise SystemExit(1)
