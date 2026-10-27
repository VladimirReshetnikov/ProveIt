#!/usr/bin/env python3
"""Replay all exact certificate/algebra checks, normally and with python -O."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def main():
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    scripts = ["portfolio.py", "verify_portfolios_independent.py",
               "verify_selector.py", "verify_schedule.py", "verify_algebra.py",
               "verify_table_width.py"]
    records = []
    for script in scripts:
        outputs = []
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT/"code"/script)]
            completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if completed.returncode:
                raise RuntimeError(script+" failed:\n"+completed.stdout+completed.stderr)
            parsed = json.loads(completed.stdout)
            canonical = json.dumps(parsed, indent=2, sort_keys=True)+"\n"
            suffix = "_optimized" if optimized else ""
            path = results / (Path(script).stem+suffix+".json")
            path.write_text(canonical, encoding="utf-8")
            outputs.append(canonical)
        if outputs[0] != outputs[1]:
            raise RuntimeError("Normal/optimized results disagree: "+script)
        records.append({"script": script, "status": "PASS", "normal_matches_optimized": True,
                        "result_sha256": hashlib.sha256(outputs[0].encode()).hexdigest()})
    result = {"status": "PASS", "standard_library_only": True,
              "checks_survive_optimization": True, "programs": records,
              "scope": "Exact finite certificates and algebra; no full SAT solver or fast MM backend"}
    encoded = json.dumps(result, indent=2, sort_keys=True)+"\n"
    (results/"verification_summary.json").write_text(encoded, encoding="utf-8")
    print(encoded, end="")


if __name__ == "__main__":
    main()
