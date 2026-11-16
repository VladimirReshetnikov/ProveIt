"""Run the exact executable diagnostics. This does not run a Lean compiler."""
import json
import platform
import subprocess
import sys
from pathlib import Path

root = Path(__file__).resolve().parent
validation = root / "validation"
validation.mkdir(exist_ok=True)
programs = ("check_categories.py", "challenge_contracts.py", "finite_descent.py", "macaulay.py")
results = []
for name in programs:
    run = subprocess.run([sys.executable, str(root / "code" / name)], cwd=root,
                         text=True, capture_output=True, check=False)
    (validation / (name.removesuffix(".py") + "_stdout.txt")).write_text(run.stdout)
    if run.stderr:
        (validation / (name.removesuffix(".py") + "_stderr.txt")).write_text(run.stderr)
    if run.returncode:
        print(run.stderr, file=sys.stderr)
        raise SystemExit(f"{name} failed with exit code {run.returncode}")
    parsed = json.loads(run.stdout)
    if name == "challenge_contracts.py":
        (validation / "contract_checks.json").write_text(json.dumps(parsed, indent=2) + "\n")
    results.append({"program": name, "exit_code": run.returncode, "results": parsed})
record = {"status": "passed", "python": platform.python_version(),
          "scope": "exact finite examples and regression diagnostics; no universal formal proof",
          "lean": "not compiled; no Lean executable available in the inspected environment",
          "programs": results}
(validation / "reproduction.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"status": record["status"], "python": record["python"],
                  "programs": [x["program"] for x in results], "lean": record["lean"]}, indent=2))
