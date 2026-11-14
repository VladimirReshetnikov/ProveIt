#!/usr/bin/env python3
"""Replay the main certificates. No sub-195 machine is claimed by this packet."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
ROOT = Path(__file__).resolve().parent
def require(ok, message):
    if not ok:
        raise ValueError(message)
def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", type=Path, help="Write a fresh receipt outside the input packet")
    ap.add_argument("--skip-hashes", action="store_true",
                    help="For an intentionally edited packet; clearly recorded in the receipt")
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, "Physical reference checks require Python without -O")
    checked_files = 0
    if not args.skip_hashes:
        manifest = json.loads((ROOT / "manifest.json").read_text())
        for name, digest in manifest["sha256"].items():
            path = ROOT / name
            require(path.is_file(), "Missing file: " + name)
            require(hashlib.sha256(path.read_bytes()).hexdigest() == digest, "Hash mismatch: " + name)
            checked_files += 1
    checks = []
    with tempfile.TemporaryDirectory(prefix="pa195-followup-replay-") as temp:
        temp = Path(temp)
        commands = [
            ("complete_machine_reconstruction_and_symbolic_runtime",
             [sys.executable, str(ROOT / "machine_195s8/verify.py")]),
            ("independent_source_quotient_and_complete_startup",
             [sys.executable, str(ROOT / "evidence/scanner8_independent_audit/independent_audit_scanner8.py"),
              str(ROOT / "machine_195s8"), str(ROOT / "reference_pa195_packet/pa195"), str(temp / "audit")]),
            ("rejected_194_negative_control", [sys.executable, str(ROOT / "verify_rejected.py")]),
            ("comparison_table_structures", [sys.executable, str(ROOT / "comparison/verify_selected_tables.py")]),
            ("source_families_and_explicit_deduction_trees", [sys.executable, str(ROOT / "source_extensions/verify.py")])
        ]
        for label, command in commands:
            print("Checking " + label + "...", flush=True)
            proc = subprocess.run(command, cwd=ROOT, text=True, capture_output=True,
                                  env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"})
            require(proc.returncode == 0, label + " failed:\n" + proc.stdout + "\n" + proc.stderr)
            checks.append({"name": label, "ok": True, "stdout": proc.stdout.strip()})
    result = {
        "ok": True,
        "requested_sub195_target_met": False,
        "validated_new_working_states": 195,
        "hashes_checked": not args.skip_hashes,
        "files_hash_checked": checked_files,
        "checks": checks,
        "not_repeated_by_this_command": [
            "exhaustive regeneration of the two-rotation search neighborhood",
            "stochastic search runs and all bounded local minimization screens",
            "end-to-end Lean/Rocq formalization of the internal PA biconditional"
        ],
        "scope": "Exact executable certificates plus a supplied ordinary mathematical transfer proof."
    }
    if args.out:
        args.out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}, indent=2))
if __name__ == "__main__":
    main()
