#!/usr/bin/env python3
"""Run every packaged exact audit and write fresh JSON files into one directory."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parents[1] / "reproduced")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    code = Path(__file__).resolve().parent
    started = time.monotonic()
    entries = []
    for name in ["brauer_audit", "idempotent_budget_audit",
                 "relation_compiler_audit", "sparse_slots_audit", "finite_bounds"]:
        command = [sys.executable, "-O", str(code / (name + ".py")),
                   "--output", str(output / (name + ".json"))]
        if name == "finite_bounds":
            command += ["--csv", str(output / "finite_bounds.csv")]
        print(f"Running {name}", flush=True)
        subprocess.run(command, check=True, cwd=code.parent)
        report = json.loads((output / (name + ".json")).read_text())
        if report.get("status") not in ("pass", "passed"):
            raise RuntimeError(f"Unsuccessful certificate from {name}")
        entries.append({"audit": name, "status": report["status"]})
    summary = {"status": "pass", "python": sys.version,
               "elapsed_seconds": round(time.monotonic() - started, 3),
               "audits": entries}
    (output / "run_summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
