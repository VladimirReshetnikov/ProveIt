#!/usr/bin/env python3
"""Reproduce the delivered checks; the mathematical proofs are in the papers."""
from pathlib import Path
import json
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    (ROOT / "provenance").mkdir(exist_ok=True)
    jobs = [
        ("independent_hidden_forms", []),
        ("recovery_demo", []),
        ("make_hidden_figure", []),
        ("check_spectral_skewness", ["--numeric"]),
    ]
    records = []
    for name, args in jobs:
        command = [sys.executable, str(ROOT / "code" / (name + ".py")), *args]
        started = time.monotonic()
        completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        log = ROOT / "provenance" / (name + "_verification.log")
        log.write_text(completed.stdout + completed.stderr, encoding="utf-8")
        records.append({
            "program": "code/" + name + ".py",
            "arguments": args,
            "returncode": completed.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "log": str(log.relative_to(ROOT)),
        })
        print(("PASS: " if completed.returncode == 0 else "FAIL: ") + name, flush=True)
        if completed.returncode:
            print(completed.stdout[-4000:] + completed.stderr[-4000:])
            break
    result = {
        "python_version": platform.python_version(),
        "all_passed": len(records) == len(jobs) and all(r["returncode"] == 0 for r in records),
        "checks": records,
        "scope": "Supplementary computation; complete mathematical proofs are supplied separately."
    }
    (ROOT / "data" / "verification_summary.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    return 0 if result["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
