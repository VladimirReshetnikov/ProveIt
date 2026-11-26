"""Replay each exact check and compare its stdout with the archived result."""
from pathlib import Path
import os
import subprocess
import sys


CHECKS = {
    "check_caps": "caps",
    "check_fields": "fields",
    "check_field_thresholds": "field_thresholds_results",
    "check_prime_blocks": "prime_block_checks",
    "check_four_prime_blocks": "four_prime_checks",
    "check_branch_poles": "branch_checks",
    "check_period": "period_checks",
    "check_fleck": "fleck_checks",
}


def main():
    root = Path(__file__).resolve().parent
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    environment.pop("PYTHONOPTIMIZE", None)
    for name, record in CHECKS.items():
        result = subprocess.run([sys.executable, str(root / "checks" / (name + ".py"))],
                                check=True, capture_output=True, text=True, env=environment)
        expected = (root / "results" / (record + ".txt")).read_text()
        if result.stdout != expected:
            raise RuntimeError(f"Output differs for {name}\n{result.stdout}")
        print(f"PASS {name}", flush=True)


if __name__ == "__main__":
    main()
