#!/usr/bin/env python3
"""Replay the exact finite checks in normal and optimized Python modes."""
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT / "code"
RESULTS = ROOT / "results"
JOBS = [
    ("certify_affine_cyclic.py", "menus_three_stage.json", False),
    ("certify_four_stage.py", "four_stage.json", False),
    ("independent_menu_audit.py", "independent_menus.json", False),
    ("independent_fourstage_audit.py", "independent_four_stage.json", False),
    ("verify_regrouping.py", "regrouping.json", False),
    ("fast_cauchy_transform.py", "kernel_checks.json", True),
]

def main():
    RESULTS.mkdir(exist_ok=True)
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    summary = {"status": "PASS", "python": platform.python_version(), "checks": []}
    with tempfile.TemporaryDirectory(prefix="sat-replay-") as temporary:
        for script, result_name, file_output in JOBS:
            outputs = []
            for optimized in (False, True):
                target = Path(temporary) / result_name
                args = [sys.executable, "-B"] + (["-O"] if optimized else [])
                args.append(str(CODE / script))
                if file_output:
                    args += ["--output", str(target)]
                run = subprocess.run(args, cwd=temporary, env=env, text=True,
                                     capture_output=True, check=True)
                data = json.loads(target.read_text() if file_output else run.stdout)
                if data.get("status") != "PASS" and not data.get("checks", {}).get("all_passed"):
                    raise RuntimeError(f"No passing result from {script}")
                outputs.append(data)
            if outputs[0] != outputs[1]:
                raise RuntimeError(f"Normal/optimized disagreement: {script}")
            reference = RESULTS / result_name
            if reference.exists() and json.loads(reference.read_text()) != outputs[0]:
                raise RuntimeError(f"Replay differs from archived certificate: {result_name}")
            for optimized, data in zip((False, True), outputs):
                suffix = "_optimized" if optimized else ""
                dest = RESULTS / (Path(result_name).stem + suffix + ".json")
                dest.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
            summary["checks"].append({"script": script, "normal": "PASS",
                                      "optimized": "PASS", "identical": True})
            print(f"PASS {script} (normal and -O)", flush=True)
    (RESULTS / "replay_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("All finite checks passed. This is not an end-to-end SAT or Lean verification.")

if __name__ == "__main__":
    main()
