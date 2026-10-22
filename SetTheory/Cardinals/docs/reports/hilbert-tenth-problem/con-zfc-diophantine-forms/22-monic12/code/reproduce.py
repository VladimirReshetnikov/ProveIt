#!/usr/bin/env python3
"""Reproduce the new finite checks using Python's standard library only.

The unbounded Diophantine equivalence is proved in the report and the inherited
references. These programs audit its finite data and algebraic implementation.
No consistency oracle, accepting K215 run, or giant coefficient expansion is used.
"""
from pathlib import Path
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STEPS = [
    ("strict_compiler.py", []),
    ("coefficient_recipe.py", []),
    ("check_strict_independent.py", []),
    ("build_mergers.py", ["--symbolic"]),
    ("build_integer26.py", []),
    ("build_retained59.py", []),
    ("check_bundle.py", []),
]


def main():
    if sys.version_info < (3, 10):
        raise SystemExit("Python 3.10 or later is required.")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    receipts = []
    for name, args in STEPS:
        command = [sys.executable, str(ROOT / "code" / name), *args]
        result = subprocess.run(command, cwd=ROOT, env=env,
                                capture_output=True, text=True)
        if result.returncode:
            sys.stdout.write(result.stdout)
            sys.stderr.write(result.stderr)
            raise SystemExit(f"FAILED: {name} (exit {result.returncode})")
        # Requiring a JSON result also catches an accidentally skipped audit.
        json.loads(result.stdout)
        receipts.append({"script": "code/" + name, "arguments": args,
                         "exit_code": 0, "status": "PASS"})
        print(f"PASS: {name}", flush=True)
    report = {
        "schema": "proveit-con-zfc-synthesis-reproduction-v1",
        "status": "PASS",
        "steps": receipts,
        "required_python": "3.10+; standard library only",
        "scope": "Finite data, circuit, algebra, and binding checks. The unbounded equivalence is an ordinary mathematical proof, not a new kernel theorem.",
    }
    (ROOT / "data" / "REPRODUCTION.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print("All seven reproduction steps passed.")


if __name__ == "__main__":
    main()
