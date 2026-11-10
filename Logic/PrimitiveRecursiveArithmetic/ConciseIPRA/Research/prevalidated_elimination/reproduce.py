"""Run the offline source census and the package's focused kernel checks.

Python 3.12 is the reference measurement runtime. No network is used.
This script never treats experimental programs as trusted kernels.
"""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def run(script):
    proc = subprocess.run([sys.executable, str(ROOT / script)], cwd=ROOT,
                          text=True, capture_output=True, timeout=180)
    if proc.returncode:
        print(proc.stdout)
        print(proc.stderr, file=sys.stderr)
        raise SystemExit(proc.returncode)
    return proc.stdout


def main():
    run("measure.py")
    run("tests/verify_kernels.py")
    if (ROOT / "tests/check_ordering.py").exists():
        run("tests/check_ordering.py")
        run("tests/check_sentinels.py")
    if (ROOT / "experiments/positive_iteration/check_positive_iteration.py").exists():
        run("experiments/positive_iteration/check_positive_iteration.py")
    metrics = json.loads((ROOT / "evidence/measurements.json").read_text())
    tests = json.loads((ROOT / "evidence/verification.json").read_text())
    print(json.dumps({
        "source_commit": metrics["commit"],
        "distinct_frozen_sources_verified": metrics["distinct_sources"],
        "programs": [{key: row[key] for key in
                      ("file", "normalized_bytes", "normalized_tokens", "ast_nodes", "gzip9_raw")}
                     for row in metrics["programs"]],
        "inherited_cli_runs": tests["inherited_cli_runs"],
        "sentinel_control_runs": tests["sentinel_control_runs"],
        "kernel_checks_passed": tests["passed"],
        "scope": "Finite tests and reproducible measurements; not proof-assistant certification"
    }, indent=2))


if __name__ == "__main__":
    main()
