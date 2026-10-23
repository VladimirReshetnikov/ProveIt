#!/usr/bin/env python3
"""Rebuild the delivered finite artifacts in an isolated copy; stdlib only.

This verifies finite certificates and reproducibility, not consistency or
the unbounded imported theorems. It never edits the delivered equation files.
"""
from pathlib import Path
from hashlib import sha256
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def relevant_files(directory):
    return sorted(p for p in directory.rglob("*")
                  if p.is_file() and "__pycache__" not in p.parts
                  and p.suffix != ".pyc")


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    require(sys.version_info >= (3, 10), "Use Python 3.10 or later.")
    groups = ["ten_integer", "coefficient_backend", "ten_integer_composed", "review"]
    steps = [
        ["ten_integer/b4_code.py"],
        ["ten_integer/build_b4_sun10.py"],
        ["ten_integer/verify_b4_sun10.py"],
        ["coefficient_backend/build_coefficients.py"],
        ["coefficient_backend/audit_coefficients.py"],
        ["coefficient_backend/verify_equations.py"],
        ["review/audit_b4_independent.py"],
        ["ten_integer_composed/regenerate_binding.py"],
        ["ten_integer_composed/b4_code.py"],
        ["ten_integer_composed/build_b4_sun10.py"],
        ["ten_integer_composed/verify_b4_sun10.py"],
        ["review/audit_composed_binding.py"],
        ["review/audit_b4_independent.py", "ten_integer_composed",
         "review/COMPOSED_B4_INDEPENDENT_AUDIT.json"],
    ]
    expected = {
        str(p.relative_to(ROOT)): digest(p)
        for group in groups for p in relevant_files(ROOT / group)
    }
    with tempfile.TemporaryDirectory(prefix="conzfc-reproduce-") as temp:
        work = Path(temp) / "package"
        work.mkdir()
        for group in groups:
            shutil.copytree(ROOT / group, work / group,
                            ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        env = os.environ.copy()
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        # Scripts resolve their own data relative to __file__.
        for index, command in enumerate(steps, 1):
            script = command[0]
            start = time.monotonic()
            print(f"[{index}/{len(steps)}] {' '.join(command)}", flush=True)
            completed = subprocess.run(
                [sys.executable, str(work / script), *command[1:]],
                cwd=work, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if completed.returncode:
                print(completed.stdout)
                raise RuntimeError(f"{script} failed with exit code {completed.returncode}")
            print(f"  PASS ({time.monotonic()-start:.2f} s)", flush=True)
        differences = [
            name for name, wanted in expected.items()
            if not (work / name).is_file() or digest(work / name) != wanted
        ]
        require(not differences, "Regenerated files differ: " + ", ".join(differences))
        main_circuit = json.loads((work / "ten_integer_composed/generated/b4_signed10.json").read_text())
        independent = json.loads((work / "review/COMPOSED_B4_INDEPENDENT_AUDIT.json").read_text())
        require(independent["status"] == "PASS", "Independent B4 audit did not pass")
        receipt = {
            "status": "PASS",
            "method": "fresh temporary copy, dependent builders followed by independent audits",
            "commands": steps,
            "existing_subpackage_files_compared": len(expected),
            "all_existing_subpackage_files_byte_identical": True,
            "main_circuit_sha256": digest(work / "ten_integer_composed/generated/b4_signed10.json"),
            "main_binding_sha256": digest(work / "ten_integer_composed/data/INSTANCE.json"),
            "main_composition_manifest_sha256": digest(work / "ten_integer_composed/COMPOSITION_BINDING.json"),
            "main_integer_variables": main_circuit["variables"],
            "main_exact_degree": independent["degree_upper_bound"],
            "main_operations": independent["operations"],
            "main_degree_attainment": independent["degree_attainment"],
            "scope": "Finite certificates and reproducibility; no consistency decision or new end-to-end formalization.",
        }
    (ROOT / "REPRODUCTION.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"PASS: all {len(expected)} existing subpackage files are unchanged.")
    print("Receipt: REPRODUCTION.json")


if __name__ == "__main__":
    main()
