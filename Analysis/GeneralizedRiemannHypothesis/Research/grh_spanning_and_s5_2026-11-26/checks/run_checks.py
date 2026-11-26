#!/usr/bin/env python3
"""Replay the three exact checkers; requires Python's standard library only."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys


def main():
    package = Path(__file__).resolve().parent.parent
    checks = package / "checks"
    cases = [
        ("integer_spanning", "verify_spanning.py", "spanning_certificates.json", True),
        ("cyclic_models", "verify_cyclic_models.py", "cyclic_models_verification.json", True),
        ("s5_characters", "check_sn5_identity.py", "sn5_verification.json", False),
    ]
    executions = []
    for name, script, output, has_output_flag in cases:
        command = [sys.executable, str(checks / script)]
        if has_output_flag:
            command.extend(["--output", str(checks / output)])
        result = subprocess.run(command, cwd=package, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        if not has_output_flag:
            json.loads(result.stdout)
            (checks / output).write_text(result.stdout)
        data = json.loads((checks / output).read_text())
        executions.append({
            "name": name,
            "script": "checks/" + script,
            "script_sha256": hashlib.sha256((checks / script).read_bytes()).hexdigest(),
            "output": "checks/" + output,
            "output_sha256": hashlib.sha256((checks / output).read_bytes()).hexdigest(),
            "return_code": result.returncode,
            "reported_status": data["status"],
        })
        print(f"PASS: {name}")
    summary = {
        "status": "PASS",
        "python": platform.python_version(),
        "upstream_commit": "72fead102f663d5c7a407964a13dc0cf9d977207",
        "prior_corpus_commit": "9816644452bb42827167d6110e6d0322315a02b9",
        "executions": executions,
        "scope": "Exact finite algebraic checks only. General proofs are in report.pdf. No upstream Lean build or new Lean proof was run.",
    }
    (package / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("PASS: verification.json written")


if __name__ == "__main__":
    main()
