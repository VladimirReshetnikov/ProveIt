#!/usr/bin/env python3
"""Replay all finite certificates normally and with Python optimization."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = ("portfolios", "schedule", "affine_algebra", "toeplitz", "lacunary")


def main():
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    records = []
    for name in CHECKS:
        outputs = []
        for optimized in (False, True):
            cmd = [sys.executable, "-B"]
            if optimized:
                cmd.append("-O")
            cmd.append(str(ROOT / "code" / ("check_" + name + ".py")))
            process = subprocess.run(cmd, cwd=ROOT, capture_output=True, check=True)
            data = json.loads(process.stdout)
            if data.get("status") != "PASS":
                raise RuntimeError("Checker did not report PASS: " + name)
            if process.stderr:
                raise RuntimeError("Unexpected checker stderr: " + name + ": " +
                                   process.stderr.decode("utf-8", errors="replace"))
            encoded = (json.dumps(data, indent=2, sort_keys=True) + "\n").encode()
            outputs.append(encoded)
            suffix = "_optimized" if optimized else ""
            (results / (name + suffix + ".json")).write_bytes(encoded)
        if outputs[0] != outputs[1]:
            raise RuntimeError("Normal and optimized results disagree: " + name)
        records.append({"checker": "code/check_" + name + ".py", "status": "PASS",
                        "normal_equals_optimized": True,
                        "result_sha256": hashlib.sha256(outputs[0]).hexdigest()})
        print(name + ": PASS (normal = optimized)", flush=True)
    report = {"status": "PASS", "checkers": records,
              "scope": "Finite certificates and exact algebra; no full SAT solver or Lean rebuild"}
    (results / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print("All five checkers passed in both modes.")


if __name__ == "__main__":
    main()
