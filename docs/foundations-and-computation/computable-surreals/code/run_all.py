#!/usr/bin/env python3
"""Rerun the three unchanged source suites and the new cross-model checks."""
from __future__ import annotations

import json
import platform
import re
import subprocess
import sys
from pathlib import Path


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    data = root / "data"
    data.mkdir(exist_ok=True)
    suites = {
        "A": ["code/original_A-verify.py", "--output", "data/A.json"],
        "B": ["code/original_B-verify.py"],
        "C": ["code/original_C-verify_examples.py"],
        "merged": ["code/verify_reconciliation.py", "--output", "data/merged.json"],
    }
    summary: dict[str, object] = {
        "python": platform.python_version(),
        "scope": "Finite tests, not formal verification; unlike units are not added together.",
        "suites": {},
    }
    failed = False
    for name, args in suites.items():
        try:
            run = subprocess.run([sys.executable, *args], cwd=root,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 text=True, encoding="utf-8", errors="replace", timeout=120)
            text, code = run.stdout, run.returncode
        except (OSError, subprocess.TimeoutExpired) as exc:
            text, code = f"Unable to finish suite: {exc}\n", 1
        (data/f"{name}.txt").write_text(text, encoding="utf-8")
        status = "PASS" if code == 0 else "FAIL"
        detail: dict[str, object] = {"status": status, "return_code": code,
                                     "log": f"data/{name}.txt"}
        if code == 0 and name in ("A", "merged"):
            payload = json.loads((data/f"{name}.json").read_text(encoding="utf-8"))
            detail.update(count=payload["total_checks"], unit="exact checks")
        elif code == 0 and name == "B":
            match = re.search(r"Ran (\d+) tests", text)
            if match:
                detail.update(count=int(match[1]), unit="named unit tests")
        elif code == 0 and name == "C":
            match = re.search(r"TOTAL: (\d+) passed; 0 failed", text)
            if match:
                detail.update(count=int(match[1]), unit="exact checks")
        summary["suites"][name] = detail  # type: ignore[index]
        failed |= code != 0
        print(f"{name}: {status}; {detail.get('count', '?')} {detail.get('unit', '')}")
        if code:
            print(text)
    summary["status"] = "FAIL" if failed else "PASS"
    (data/"summary.json").write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
