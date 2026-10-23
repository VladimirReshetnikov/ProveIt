#!/usr/bin/env python3
"""Rebuild and verify the distributed finite artifacts, offline.

These checks establish the stated finite identities and metrics. They do
not verify an unbounded compiler theorem or prove ZFC consistency.
"""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    commands = [
        ["upstream44/native/build_coefficients.py"],
        ["-O", "upstream44/native/audit_coefficients.py"],
        ["upstream31/coefficients/build_coefficients.py"],
        ["research_nine/compact_candidate/build_nine.py"],
        ["research_nine/candidate/build_nine.py"],
        ["-O", "research_low_degree/audit_gap_source.py"],
        ["-O", "research_alternatives/check_positive_gap.py",
         "--records", "research_nine/compact_candidate/data/parent_source.json",
         "--layout", "research_nine/compact_candidate/data/split_code.json"],
        ["research_nine/compact_candidate/write_source_table.py"],
        ["-O", "research_nine/compact_candidate/audit_circuit.py",
         "--binding", "upstream44/native/COEFFICIENT_BINDING.json"],
        ["research_low_degree/supplement15/build.py"],
        ["-O", "research_low_degree/supplement15/verify.py"],
    ]
    receipts = []
    for index, args in enumerate(commands, 1):
        result = subprocess.run(
            [sys.executable, *args], cwd=ROOT,
            env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
            text=True, capture_output=True)
        log_name = "replay_%02d.log" % index
        (ROOT / "checks" / log_name).write_text(result.stdout + result.stderr)
        receipts.append({
            "command": ["python3", *args],
            "exit_code": result.returncode,
            "log": "checks/" + log_name,
        })
        print(("PASS" if result.returncode == 0 else "FAIL") +
              " " + " ".join(args), flush=True)
        if result.returncode:
            print(result.stdout + result.stderr)
            raise SystemExit(result.returncode)

    files = [
        "research_nine/compact_candidate/generated/gap_100_positive.json",
        "research_nine/compact_candidate/generated/gap_100_natural.json",
        "research_nine/compact_candidate/generated/gap_100_positive_certificate_degree.json",
        "research_nine/compact_candidate/generated/INDEPENDENT_CIRCUIT_AUDIT.json",
        "research_alternatives/positive_gap_independent_check.json",
        "research_low_degree/gap_source_audit.json",
        "research_low_degree/supplement15/certificates/VERIFY.json",
    ]
    report = {
        "status": "PASS", "commands": receipts,
        "key_file_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in files
        },
        "scope": (
            "Offline finite algebra, coefficient, circuit and degree audits. "
            "No end-to-end Lean/Rocq run, object-language ZFC derivation, "
            "consistency decision or witness search is certified."
        ),
    }
    (ROOT / "checks" / "REPRODUCTION.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print("All finite artifact checks passed.")


if __name__ == "__main__":
    main()
