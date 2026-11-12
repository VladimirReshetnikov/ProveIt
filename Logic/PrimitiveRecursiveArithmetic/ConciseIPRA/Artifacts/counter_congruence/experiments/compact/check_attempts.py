"""Finite canonical and boundary smoke tests for the nonwinning experiments."""
import copy
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
r = [[0], 0, 3]
eq = [r, 0]
arith = [0, r, 0]
rl = [eq, 0, []]
paired = [0, 0, [0, 0]]
positive = {
    "R0": [[0, [0, 0, 0], 0], [[0, 0, 0], [0]]],
    "RS_counter": [arith, eq],
    "RS_state": [[0, [[0], 0, 1], 0], [[[0], 0, 1], [0, 0, 1]]],
    "RL_reflexivity": [arith, arith, rl, [0, 0]],
    "CC": [arith, [eq, 0, [0, 0]], [[r, 0, 0], [0, 0, 0]]],
    "DI_constant_equation": [[0, 0, [0]], paired],
    "DE_QE": [arith, arith, rl, [[[0, 0]], 0, [0]],
               [0, 0, [0]], [paired, 0, 0], [0, 0]],
}
negative = {}
x = copy.deepcopy(positive["R0"])
x[-1][1] = 0
negative["wrong_R0"] = x
x = copy.deepcopy(positive["CC"])
x[-1][0][1] = [0]
negative["CC_seed_change"] = x
x = copy.deepcopy(positive["CC"])
x[-1][0][2] = [0]
negative["CC_update_change"] = x
negative["binary_counter_constant_update"] = [[0, [[0, 0], 0, [0]], 0], [[[0, 0], 0, [0]], [0]]]
negative["escaped_update_coordinate"] = [[0, [[0], 0, 5], 0], [[[0], 0, 5], 0]]
negative["unallocated_goal_parameter"] = [[-1, -1]]

rows = []
for file in ("counter_compact.py", "fused_facts.py"):
    for expected, cases in ((True, positive), (False, negative)):
        for name, packet in cases.items():
            for optimized in (False, True):
                args = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / file)]
                run = subprocess.run(args, input=json.dumps(packet), text=True,
                                     capture_output=True, timeout=15)
                actual = run.returncode == 0 and run.stdout == "ACCEPT\n"
                rows.append({"file": file, "case": name, "optimized": optimized,
                             "expected": expected, "actual": actual,
                             "passed": actual == expected, "exit": run.returncode,
                             "stdout": run.stdout, "stderr": run.stderr})
receipt = {"runs": len(rows), "passed": all(r["passed"] for r in rows),
           "scope": "Finite smoke and targeted boundary tests only; not universal certification of raw aliases.",
           "rows": rows}
(ROOT / "smoke_tests.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({k:v for k,v in receipt.items() if k != "rows"}, indent=2))
if not receipt["passed"]:
    print(json.dumps([row for row in rows if not row["passed"]], indent=2))
    raise SystemExit(1)
