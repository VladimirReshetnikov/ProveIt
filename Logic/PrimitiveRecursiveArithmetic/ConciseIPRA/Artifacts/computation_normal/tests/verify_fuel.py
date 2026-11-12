"""Exercise the explicit-fuel interface on genuine proof certificates."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
case = json.loads((ROOT / "certificates/full_normal_case.json").read_text())
program = ROOT / "code/full_normal_fuel.py"
results = []
for fuel, expected in [(1000, True), (0, False), (-1, False), (True, False), (1.5, False)]:
    for optimized in (False, True):
        certificate = dict(case, fuel=fuel)
        command = [sys.executable, "-I", "-S", "-B"] + (["-O"] if optimized else []) + [str(program)]
        process = subprocess.run(command, input=json.dumps(certificate).encode(),
                                 capture_output=True, timeout=20)
        accepted = process.returncode == 0 and process.stdout == b"ACCEPT\n"
        results.append({"fuel": fuel, "optimized": optimized, "expected": expected,
                        "accepted": accepted, "passed": accepted == expected})
if not all(row["passed"] for row in results):
    raise AssertionError(results)
(ROOT / "evidence/fuel_verification.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps({"fuel_process_checks": len(results), "failures": 0}))
