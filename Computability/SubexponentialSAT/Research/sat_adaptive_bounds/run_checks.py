#!/usr/bin/env python3
"""Run the delivered mathematical certificates in normal and optimized Python."""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def mathematical_part(value):
    if isinstance(value, dict):
        return {k: mathematical_part(v) for k, v in value.items()
                if k != "elapsed_seconds"}
    if isinstance(value, list):
        return [mathematical_part(v) for v in value]
    return value


def main():
    results = ROOT / "results"
    results.mkdir(exist_ok=True)
    summary = {"status": "passed", "suites": []}
    for script, stem in [
        ("verify_cached_results.py", "cached_results"),
        ("verify_flags.py", "flag_verification"),
    ]:
        outputs = []
        for optimized in (False, True):
            command = [sys.executable]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / "code" / script))
            completed = subprocess.run(command, cwd=ROOT, text=True,
                                       capture_output=True, check=True)
            output = json.loads(completed.stdout)
            target = results / (stem + ("_optimized" if optimized else "") + ".json")
            target.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
            outputs.append(mathematical_part(output))
        if outputs[0] != outputs[1]:
            raise RuntimeError(f"Normal/optimized mathematical results differ: {script}")
        summary["suites"].append({"script": script,
                                 "normal": "passed",
                                 "optimized": "passed",
                                 "mathematical_outputs_equal": True})
        print(f"{script}: normal and optimized checks passed", flush=True)
    (results / "verification_summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print("All delivered finite certificates passed.")


if __name__ == "__main__":
    main()
