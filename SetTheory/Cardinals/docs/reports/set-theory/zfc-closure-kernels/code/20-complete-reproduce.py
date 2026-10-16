#!/usr/bin/env python3
"""Run the offline research checks and compare the two regenerated machines.

This checks research artifacts; it does not build Coq/Lean, prove ZFC
consistent, or certify a new end-to-end consistency machine.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_table(path: Path, states: int) -> dict:
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        q, read, write, direction, target = line.split()
        q, read, write, target = map(int, (q, read, write, target))
        if ((q, read) in rows or read not in (0, 1) or write not in (0, 1)
                or direction not in ("L", "R") or not 0 <= target <= states):
            raise ValueError("Invalid or duplicate literal transition")
        rows[q, read] = (write, direction, target)
    if set(rows) != {(q, b) for q in range(states) for b in (0, 1)}:
        raise ValueError("Incomplete working-state table")
    return {"working_states": states, "rows": len(rows), "sha256": sha(path),
            "status": "literal structure/count only; no endpoint theorem"}


def main() -> None:
    if not __debug__:
        raise SystemExit("Run without -O/-OO; some executable checks require assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        help="Scratch result directory; defaults to a new temporary directory")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    out = (args.output or Path(tempfile.mkdtemp(prefix="zfc-reproduction-"))).resolve()
    out.mkdir(parents=True, exist_ok=True)
    jobs = [
        ("reference", ["code/check_reference.py", "--output", str(out / "reference_checks.json"),
                       "--examples", str(out / "examples")]),
        ("low_codes", ["code/check_low_codes.py", "--output", str(out / "low_code_epsc_checks.json")]),
        ("closed_falsity", ["code/check_closed_falsity.py", "--output", str(out / "closed_falsity_checks.json")]),
        ("epsc271", ["code/reproduce_epsc271.py", "--output", str(out / "epsc271")]),
        ("decoder255", ["code/reproduce_decoder255.py", "--output", str(out / "decoder255")]),
    ]
    result = {"scope": "offline finite artifact checks; no new formal machine endpoint", "jobs": {}}
    task_env = os.environ.copy()
    task_env["PYTHONDONTWRITEBYTECODE"] = "1"
    for name, command in jobs:
        print(f"Running {name} ...", flush=True)
        with (out / (name + ".log")).open("w") as log:
            run = subprocess.run([sys.executable, *command], cwd=root,
                                 stdout=log, stderr=subprocess.STDOUT, env=task_env)
        result["jobs"][name] = {"exit_code": run.returncode, "log": name + ".log"}
        if run.returncode:
            (out / "summary.json").write_text(json.dumps(result, indent=2) + "\n")
            raise SystemExit(f"{name} failed; inspect {out / (name + '.log')}")
    for name in ("reference_checks", "low_code_epsc_checks", "closed_falsity_checks"):
        if json.loads((out / (name + ".json")).read_text()) != json.loads((root / "data" / (name + ".json")).read_text()):
            raise ValueError("Delivered and regenerated result differ: " + name)
    result["regenerated_result_json_equal"] = True
    result["tables"] = {}
    for name, states in (("epsc271", 271), ("decoder255", 255)):
        delivered = root / "machines" / (name + ".tm")
        generated = out / name / (name + ".tm")
        if delivered.read_bytes() != generated.read_bytes():
            raise ValueError("Generated table differs: " + name)
        result["tables"][name] = inspect_table(delivered, states) | {"regenerated_exactly": True}
    result["tables"]["epsc276_comparison"] = inspect_table(root / "machines/epsc276_comparison.tm", 276)
    result["tables"]["epsc276_comparison"]["regenerated_exactly"] = False
    result["status"] = "PASS"
    (out / "summary.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    print(f"Results: {out}")


if __name__ == "__main__":
    main()
