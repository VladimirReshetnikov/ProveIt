"""Run all exact local certificates and prototypes; standard library only."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    jobs = [
        ("verify_covariance.py", "covariance_certificate.json"),
        ("verify_schedule.py", "schedule_results.json"),
        ("verify_separator.py", "separator_results.json"),
        ("verify_separator_covariance_independent.py", "separator_covariance_independent.json"),
        ("verify_group_contraction.py", None),
        ("verify_tree_selector.py", None),
        ("verify_incidence_obstruction.py", "incidence_obstruction_results.json"),
    ]
    outputs = []
    (ROOT / "results").mkdir(exist_ok=True)
    for script, filename in jobs:
        completed = subprocess.run([sys.executable, str(ROOT / "code" / script)],
                                   cwd=ROOT, text=True, capture_output=True)
        if completed.returncode:
            sys.stderr.write(completed.stderr)
            sys.stderr.write(completed.stdout)
            raise RuntimeError(f"certificate failed: {script}")
        value = json.loads(completed.stdout)
        if filename:
            (ROOT / "results" / filename).write_text(json.dumps(value, indent=2) + "\n")
        outputs.append({"script": script, "exit_code": completed.returncode})
        print(f"PASS {script}", flush=True)
    summary = {"status": "pass", "checks": outputs,
               "scope": "Exact finite certificates and local algorithms; no end-to-end SAT solver or imported fast-matrix backend is tested."}
    (ROOT / "results" / "verification_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n")
    print("All seven certificate/prototype programs passed.")


if __name__ == "__main__":
    main()
