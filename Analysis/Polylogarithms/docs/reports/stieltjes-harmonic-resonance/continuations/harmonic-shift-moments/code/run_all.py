#!/usr/bin/env python3
"""Run the article's reproducible checks with the current Python interpreter.

Each mathematical checker retains its own readable JSON result. Numerical
checks are diagnostics, not interval certificates. No network is used.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = (
    "verify_shift_germs",
    "verify_shift_primitives",
    "verify_bell_moments",
    "verify_harmonic_powers",
    "verify_collisions",
    "derive_polygamma_collisions",
    "verify_polygamma_collisions",
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list checkers without running")
    parser.add_argument("--only", nargs="+", choices=SCRIPTS, help="run selected checkers")
    args = parser.parse_args()
    selected = args.only or SCRIPTS
    if args.list:
        print("\n".join(selected))
        return
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    reports = []
    for name in selected:
        script = ROOT / "code" / f"{name}.py"
        if not script.is_file():
            raise SystemExit(f"Missing checker: {script}")
        print(f"Running {name} ...", flush=True)
        started = time.monotonic()
        completed = subprocess.run(
            [sys.executable, str(script)], cwd=ROOT,
            capture_output=True, text=True, check=False,
        )
        log = results / f"{name}.log"
        log.write_text(completed.stdout + completed.stderr, encoding="utf-8")
        report = {
            "checker": name,
            "exit_code": completed.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": str(log.relative_to(ROOT)),
        }
        reports.append(report)
        (results / "verification_run.json").write_text(
            json.dumps({"checks": reports, "all_passed": all(x["exit_code"] == 0 for x in reports)}, indent=2) + "\n",
            encoding="utf-8",
        )
        if completed.returncode:
            print(completed.stdout)
            print(completed.stderr, file=sys.stderr)
            raise SystemExit(completed.returncode)
        print(f"Passed {name} ({report['elapsed_seconds']} seconds)", flush=True)
    print(f"All {len(reports)} selected checkers passed.")


if __name__ == "__main__":
    main()
