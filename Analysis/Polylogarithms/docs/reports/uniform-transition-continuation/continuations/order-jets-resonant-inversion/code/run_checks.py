#!/usr/bin/env python3
"""Reproduce the report's diagnostics without replacing the recorded data."""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import time

PROGRAMS = {
    "local": ("verify_local_jets.py", "verification_local_jets.json"),
    "borel": ("verify_borel_jets.py", "borel_verification.json"),
    "complex": ("verify_complex_resonance.py", "complex_resonance_checks.json"),
    "principal": ("verify_principal_sheet.py", "principal_sheet_check.json"),
}

def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=root / "verification_run")
    parser.add_argument("--only", nargs="+", choices=PROGRAMS, default=list(PROGRAMS))
    args = parser.parse_args()
    destination = args.output_dir.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    runs = []
    for name in args.only:
        script, filename = PROGRAMS[name]
        command = [sys.executable, str(root / "code" / script),
                   "--output", str(destination / filename)]
        print("Running " + name + " diagnostics...", flush=True)
        start = time.perf_counter()
        result = subprocess.run(command, cwd=root, text=True, capture_output=True)
        log_path = destination / (name + ".log")
        log_path.write_text(result.stdout + result.stderr)
        entry = {"name": name, "exit_code": result.returncode,
                 "elapsed_seconds": time.perf_counter() - start,
                 "result_file": filename, "log_file": log_path.name}
        runs.append(entry)
        print(json.dumps(entry), flush=True)
        if result.returncode:
            (destination / "run_summary.json").write_text(
                json.dumps({"runs": runs, "status": "failed"}, indent=2) + "\n")
            raise SystemExit(result.returncode)
    (destination / "run_summary.json").write_text(
        json.dumps({"runs": runs, "status": "completed",
                    "interpretation": "Diagnostics, not interval certificates."},
                   indent=2) + "\n")

if __name__ == "__main__":
    main()
