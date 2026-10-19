#!/usr/bin/env python3
"""Reproduce the exact 239-state mathematical checks in a fresh directory.

No proof-assistant compilation or replay of the inherited logical calibration
is performed. The default includes the complete unbounded 239-table runtime
proof. --quick deliberately omits that proof and reports a partial status.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import os
import shutil
import subprocess
import sys
import time

if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
    raise RuntimeError("Use Python with assertions enabled and PYTHONOPTIMIZE unset.")
ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--with-guard", action="store_true")
    args = ap.parse_args()
    out = args.output.resolve()
    if out.exists() and any(out.iterdir()):
        ap.error("Choose a new or empty output directory; existing evidence is not overwritten.")
    out.mkdir(parents=True, exist_ok=True)
    records = []
    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"

    def run(name, script, arguments, receipt, status):
        command = [sys.executable, "-B", str(script), *map(str, arguments)]
        print(f"Checking {name} ...", flush=True)
        started = time.monotonic()
        with (out / f"{name}.log").open("w") as log:
            completed = subprocess.run(command, cwd=ROOT, env=env,
                                       stdout=log, stderr=subprocess.STDOUT)
        if completed.returncode:
            raise RuntimeError(f"{name} failed; see {out / (name + '.log')}")
        data = json.loads(receipt.read_text())
        if data.get("status") != status:
            raise RuntimeError(f"{name}: expected {status}, got {data.get('status')}; see {receipt}")
        records.append({"check": name, "status": status, "seconds": time.monotonic() - started,
                        "receipt": str(receipt.relative_to(out)),
                        "receipt_sha256": sha256(receipt.read_bytes()).hexdigest()})
        print(f"  {status}", flush=True)
        return data

    v = ROOT / "verification"
    old, new, sites = ROOT / "reference/zfc240_old.tm", ROOT / "machines/zfc239_old.tm", ROOT / "machines/sites_logical.json"
    run("construction", v / "verify_construction.py", ["--output", out / "construction.json"],
        out / "construction.json", "EXACT_CONSTRUCTION_AND_RENUMBERING_PASS")
    run("source_joins", v / "verify_source_joins.py", ["--output", out / "source_joins.json"],
        out / "source_joins.json", "COMPLETE_SOURCE_TREE_AND_PADDING_JOINS_PASS")
    run("boot_clock", v / "verify_boot_clock.py", ["--output", out / "boot_clock.json"],
        out / "boot_clock.json", "EXACT_239_CANONICAL_BOOT_AND_CLOCK_PASS")
    run("local", v / "verify_local239.py", ["--baseline", old, "--candidate", new, "--output", out / "local.json"],
        out / "local.json", "EXACT_SYMBOLIC_LOCAL_PASS")
    run("independent_local", v / "review_local239.py",
        ["--baseline", old, "--candidate", new, "--certificate", out / "local.json", "--output", out / "independent_local.json"],
        out / "independent_local.json", "INDEPENDENT_FREE_EXTERIOR_CERTIFICATE_REPLAY_PASS")
    run("independent_boot", v / "verify_boot_independent.py",
        ["--baseline", old, "--output", out / "bootstrap"],
        out / "bootstrap/boot_v106.json", "TWO_INTERPRETER_EXACT_BLANK_BOOT_PASS")

    # The standalone matrix checker writes beside itself. Copy it so its new
    # evidence is kept in the replay directory and archived evidence stays exact.
    logic_dir = out / "formalisms"
    logic_dir.mkdir()
    logic_script = logic_dir / "check_specialization_obstructions.py"
    shutil.copyfile(ROOT / "research/formalisms/check_specialization_obstructions.py", logic_script)
    run("logical_matrices", logic_script, [], logic_dir / "specialization_obstructions.json", "PASS")

    if not args.quick:
        data = run("runtime", v / "symbolic_runtime.py",
            ["--table", new, "--sites", sites, "--output", out / "runtime.json"],
            out / "runtime.json", "UNIVERSAL_MATHEMATICAL_PASS")
        assert data["cases"] == data["expected_cases"] == 8386
        assert data["input_validation"]["working_states"] == 239
        assert len(data["directly_used_rows"]) == 478 and data["minimum_actual_steps"] > 0
        assert data["table_sha256"] == sha256(new.read_bytes()).hexdigest()
    if args.with_guard:
        data = run("selector_guard", v / "verify_selector_guard.py",
            ["--checker", v / "symbolic_runtime.py", "--table", old, "--sites", sites,
             "--output", out / "selector_guard.json"],
            out / "selector_guard.json", "UNBOUNDED_SELECTOR_GUARD_PASS")
        assert data["complete_cases"] == 8386 and data["minimum_right_one_run"] >= 2
    result = {
        "status": ("QUICK_ARTIFACT_CHECKS_PASS_UNBOUNDED_REPLAY_OMITTED" if args.quick
                   else "FULL_239_MATHEMATICAL_REPLAY_PASS"),
        "complete_239_runtime_replayed": not args.quick,
        "additional_predecessor_guard_replayed": args.with_guard,
        "records": records,
        "scope": "Exact construction, source identity and joins, whole blank frame, local proof replay, and (unless --quick) all unbounded 239 runtime cases. The source's logical consistency calibration is inherited; no new Lean/Rocq or internal PA endpoint is claimed.",
        "driver_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (out / "reproduction.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
