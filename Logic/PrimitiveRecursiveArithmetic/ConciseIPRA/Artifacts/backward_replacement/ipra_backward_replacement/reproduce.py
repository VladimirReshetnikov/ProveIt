"""Run the included checker regressions and collate their evidence."""
import json
import platform
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    commands = [
        "backward/test_checker.py",
        "backward/independent_audit.py",
        "backward/compare_checkers.py",
        "grouped/verify.py",
    ]
    for name in commands:
        result = subprocess.run(
            [sys.executable, str(ROOT / name)], cwd=ROOT,
            capture_output=True, text=True, timeout=120,
        )
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        print(name + ": PASS")
    data = {
        "python": platform.python_version(),
        "all_suites_passed": True,
        "reference_checker": json.loads((ROOT / "backward/test_results.json").read_text()),
        "independent_audit": json.loads((ROOT / "backward/independent_audit_results.json").read_text()),
        "matched_comparison": json.loads((ROOT / "backward/comparison.json").read_text()),
        "grouped_protocol": json.loads((ROOT / "grouped/evidence/results.json").read_text()),
        "claim": "No construction below all three incumbent compact minima is established.",
    }
    (ROOT / "evidence/reproduction.json").write_text(json.dumps(data, indent=2) + "\n")
    print("All executable evidence reproduced.")


if __name__ == "__main__":
    main()
