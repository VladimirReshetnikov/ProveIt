#!/usr/bin/env python3
"""Independent finite checks, not universal proofs or formal certificates."""
from __future__ import annotations
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

def main() -> None:
    root = Path(__file__).resolve().parents[1]
    validation = root / "validation"
    validation.mkdir(exist_ok=True)
    scripts = ["machine_checks.py", "reduction_checks.py", "space_checks.py",
               "random_lower_checks.py", "quantum_checks.py"]
    results = []
    for script in scripts:
        start = time.monotonic()
        proc = subprocess.run([sys.executable, str(root / "code" / script)],
                              cwd=root, text=True, capture_output=True, check=False)
        elapsed = time.monotonic() - start
        out = proc.stdout + proc.stderr
        log = validation / (Path(script).stem + ".log")
        log.write_text(out, encoding="utf-8")
        try:
            details = json.loads(proc.stdout)
        except json.JSONDecodeError:
            details = {"detail_log": str(log.relative_to(root))}
        record = {"script": "code/" + script, "exit_code": proc.returncode,
                  "elapsed_seconds": round(elapsed, 3),
                  "result": "passed" if proc.returncode == 0 else "failed",
                  "details": details}
        results.append(record)
        print(f"{script}: {record['result']} ({elapsed:.2f}s)", flush=True)
    summary = {
        "overall": "passed" if all(r["exit_code"] == 0 for r in results) else "failed",
        "python": platform.python_version(), "checks": results,
        "verification_boundary": "Finite implementation checks only. New Lean files uncompiled; no completed object-iPRA derivations or asymptotic resource certificates are claimed."
    }
    (validation / "aggregate.json").write_text(json.dumps(summary, indent=2) + "\n")
    if summary["overall"] != "passed":
        raise SystemExit(1)

if __name__ == "__main__":
    main()
