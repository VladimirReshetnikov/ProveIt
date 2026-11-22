#!/usr/bin/env python3
"""Run the finite exact-arithmetic examples; do not conflate them with proofs."""
from pathlib import Path
import hashlib
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if sys.flags.optimize:
        raise SystemExit("Run without -O: the example checks use assertions.")
    jobs = [
        ("budget", "budget_reference.py", []),
        ("measure", "measure_reference.py", ["--output", str(ROOT / "evidence/measure_checks.json")]),
        ("probability", "probability_models.py", []),
        ("analytic", "analytic_reference.py", []),
        ("homotopy", "check_chain_contraction.py", []),
    ]
    records = []
    for name, filename, args in jobs:
        path = ROOT / "code" / filename
        start = time.monotonic()
        run = subprocess.run([sys.executable, str(path), *args], cwd=ROOT,
                             capture_output=True, text=True)
        record = {"name": name, "source": str(path.relative_to(ROOT)),
                  "sha256": sha256(path), "exit_code": run.returncode,
                  "seconds": round(time.monotonic() - start, 4)}
        if run.returncode:
            record.update(stdout=run.stdout, stderr=run.stderr)
            records.append(record)
            (ROOT / "evidence/integration_checks.json").write_text(
                json.dumps({"status": "failed", "checks": records}, indent=2) + "\n")
            raise SystemExit(f"{filename} failed:\n{run.stdout}\n{run.stderr}")
        record["summary"] = json.loads(run.stdout)
        if name == "probability":
            (ROOT / "evidence/probability_checks.json").write_text(
                json.dumps(record["summary"], indent=2) + "\n")
        records.append(record)
        print(f"{name}: passed")
    receipt = {"status": "passed", "python": platform.python_version(),
               "arithmetic": "exact rational/integer acceptance checks",
               "scope": "finite implementation validation, not universal proofs or iPRA derivations",
               "checks": records}
    (ROOT / "evidence/integration_checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("All five finite example programs passed.")


if __name__ == "__main__":
    main()
