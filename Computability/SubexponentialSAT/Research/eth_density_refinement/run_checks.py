#!/usr/bin/env python3
"""Reproduce all component checks without invoking a full SAT solver."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
RESULTS = ROOT / "results"

def main():
    RESULTS.mkdir(exist_ok=True)
    subprocess.run(
        [sys.executable, str(ROOT / "checks/density_checks.py"),
         "--output", str(RESULTS / "density_checks.json")],
        cwd=ROOT, check=True)
    for script, output in [
        ("check_retuning.py", "retuning_checks.json"),
        ("check_smith.py", "smith_checks.json"),
    ]:
        completed = subprocess.run(
            [sys.executable, str(ROOT / "checks" / script)],
            cwd=ROOT, check=True, text=True, capture_output=True)
        result = json.loads(completed.stdout)
        (RESULTS / output).write_text(
            json.dumps(result, indent=2) + "\n", encoding="utf-8")
        print(script, result.get("status", "completed"))
    print("All component checks passed. These are not a full-solver verification.")

if __name__ == "__main__":
    main()

