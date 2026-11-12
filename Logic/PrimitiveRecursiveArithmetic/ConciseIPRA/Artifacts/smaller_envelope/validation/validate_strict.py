"""Check the readable strict companion's proof and public-input boundaries."""
import ast
import copy
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
checker = root / "checkers/readable_strict.py"
tree = ast.parse(checker.read_text())
tree.body = [x for x in tree.body if isinstance(x, ast.FunctionDef)]
namespace = {}
exec(compile(tree, str(checker) + ":grammar", "exec"), namespace)
public_formula = namespace["public_formula"]
integer_list_tree = namespace["integer_list_tree"]
manifest = json.loads((root / "fixtures/manifest.json").read_text())
cases = []
for item in manifest["cases"]:
    if not item["path"].startswith("fixtures/zero/"):
        continue
    data = json.loads((root / item["path"]).read_text())
    valid_goal = (type(data) is list and bool(data)
                  and integer_list_tree(data) and public_formula(data[-1]))
    cases.append((item["name"], data, bool(valid_goal and item["expected"])))
positive = next(copy.deepcopy(data) for _, data, expected in cases if expected)
for name, prefix in [("Boolean leaf", True), ("float leaf", 0.0),
                     ("string leaf", "unused"), ("object leaf", {})]:
    cases.append(("reject_prefix_" + name, [prefix] + positive, False))
cases += [("empty_certificate", [], False),
          ("empty_truth_public_alias", [[0, 0, 0, 0], [[]]], False),
          ("bare_false_goal", [[0, [0]]], False)]
receipts = []
failures = []
for name, data, expected in cases:
    for optimized in [False, True]:
        command = [sys.executable] + (["-O"] if optimized else []) + [str(checker)]
        result = subprocess.run(command, input=json.dumps(data).encode(),
                                capture_output=True, timeout=20)
        accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
        row = {"name": name, "optimized": optimized,
               "expected": expected, "accepted": accepted}
        receipts.append(row)
        if accepted != expected:
            failures.append(row)
report = {"fixture_cases": len(cases), "process_executions": len(receipts),
          "accepted_runs": sum(x["accepted"] for x in receipts),
          "failures": failures, "results": receipts,
          "scope": "Exact integer/list input and closed guarded public goals; larger companion"}
(root / "evidence/strict_validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
if failures:
    raise SystemExit(1)
