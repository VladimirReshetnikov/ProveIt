#!/usr/bin/env python3
"""Reproduce the Prefix247 construction and all packaged mathematical checks.

Only Python's standard library is needed. Reference250 stays unchanged.
The fresh results are written under results/. The universal statements use
the word/list induction proofs and symbolic-rule interpretation in report.tex;
the literal regression checks are deliberately identified as finite tests.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Assertions are required; do not use Python -O or -OO.")

from datetime import datetime, timezone
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
REFERENCE = ROOT / "reference250"


def read_json(path):
    data = json.loads(path.read_text())
    assert data.get("status") == "PASS", (path, data.get("status"))
    return data


def execute(name, arguments, records):
    started = time.monotonic()
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    command = [sys.executable, "-B", *map(str, arguments)]
    result = subprocess.run(command, cwd=ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(name + "\n" + result.stdout[-2000:] + result.stderr[-6000:])
    records.append(dict(name=name, status="PASS", seconds=round(time.monotonic()-started, 6),
                        command=["python3", "-B", *map(str, arguments)]))
    print("PASS", name, flush=True)


def main():
    RESULTS.mkdir(exist_ok=True)
    started = time.monotonic()
    records = []

    # Rebuild the inherited table from the bundled, independently pinned 252
    # table; this prevents an unexplained 250-table dependency.
    sys.path.insert(0, str(REFERENCE / "code"))
    import rebuild_machines
    inherited = rebuild_machines.encode(rebuild_machines.build(), 97).encode("ascii")
    assert inherited == (REFERENCE / "machine/zfc_prefix250_old.tm").read_bytes()
    records.append(dict(name="inherited_252_to_250_reconstruction", status="PASS"))
    print("PASS inherited_252_to_250_reconstruction", flush=True)
    execute("complete_report_transition_table", ["code/build_table.py", "--check"], records)

    with tempfile.TemporaryDirectory(prefix="prefix247-verify-") as tmp:
        temp = Path(tmp)
        execute("dual_literal_bootstrap_and_table_quotient", ["code/audit247.py",
                "--source", "reference250/machine/zfc_prefix250_old.tm", "--output", temp], records)
        for name in ("zfc_prefix247_old.tm", "zfc_prefix247.tm", "renumbering247.json"):
            assert (temp / name).read_bytes() == (ROOT / "machine" / name).read_bytes(), name
        for name in ("bootstrap247.json", "bootstrap247-row-visits.json"):
            shutil.copyfile(temp / name, RESULTS / name)

    execute("unbounded_macro_inductions_and_all_instruction_cases", [
        "code/verify_runtime247.py", "--reference250", "reference250",
        "--candidate247", "machine/zfc_prefix247_old.tm", "--output", "results"], records)
    runtime = read_json(RESULTS / "runtime247_result.json")
    assert runtime["induction_templates"]["status"] == "PASS"
    assert runtime["runtime"]["guarded_cases"] == 8391
    for name in ("zfc_prefix247_old.tm", "zfc_prefix247.tm"):
        assert (RESULTS / name).read_bytes() == (ROOT / "machine" / name).read_bytes()
        (RESULTS / name).unlink()

    execute("independent_full_source_and_full_pc", ["code/check_full_source247.py",
        "--program", "reference250/sources/Prog254.v",
        "--sites", "reference250/sources/prior/instruction-sites-physical.json",
        "--table", "machine/zfc_prefix247_old.tm",
        "--checker", "reference250/code/affine_engine.py",
        "--output", "results/full-source247.json"], records)
    full_source = read_json(RESULTS / "full-source247.json")

    execute("finite_literal_instruction_regressions", [
        "reference250/code/check_literal_instructions.py",
        "--baseline", "reference250/sources/baseline252_old.tm",
        "--program", "reference250/sources/Prog254.v",
        "--table", "machine/zfc_prefix247_old.tm",
        "--output", "results/literal-instructions247.json"], records)
    instructions = read_json(RESULTS / "literal-instructions247.json")

    execute("finite_literal_arithmetic_regressions", [
        "reference250/code/check_literal_macros.py",
        "--table", "machine/zfc_prefix247_old.tm",
        "--output", "results/literal-macros247.json"], records)
    macros = read_json(RESULTS / "literal-macros247.json")
    boot = read_json(RESULTS / "bootstrap247.json")

    result = dict(status="PASS", finished_utc=datetime.now(timezone.utc).isoformat(),
        python_version=platform.python_version(), assertions_enabled=True,
        elapsed_seconds=round(time.monotonic()-started, 6), checks=records,
        exact_machine=dict(working_states=247, binary_rows=494, start=0, halt=247,
            old_start=97, old_halt=254, canonical_dispatch=89,
            sha256=sha256((ROOT / "machine/zfc_prefix247.tm").read_bytes()).hexdigest()),
        bootstrap=dict(steps=boot["bootstrap_steps"], dual_simulators=True,
            head=boot["head"], marker=boot["marker"], header=boot["header"],
            gap=boot["gap"], primary=boot["logical_primary"], spares=boot["spare_count"],
            one_cells=boot["one_count"], entire_tape_checked=True),
        universal_checks=dict(block_inductions=4, arithmetic_macros=3, selector_macros=9,
            source_nodes=6459, source_leaves=6460, guarded_cases=8391,
            minimum_literal_progress=runtime["runtime"]["minimum_literal_progress"],
            deleted_state_lookups=0,
            full_source_and_full_pc=full_source["universal_guarded_recheck"]),
        finite_regressions=dict(instruction_cases=instructions["cases"],
            instruction_steps=instructions["literal_steps"],
            arithmetic_cases=macros["total_cases"], arithmetic_steps=macros["literal_steps"]),
        proof_assistant_endpoint_checked=False, logical_dependency_closure_rebuilt=False,
        serialized_zfc_derivation_supplied=False, pa_internal_proof_supplied=False,
        nonhalting_inferred_from_finite_testing=False)
    (RESULTS / "verification-summary.json").write_text(json.dumps(result, indent=2)+"\n")
    print("PASS all checks; results/verification-summary.json", flush=True)


if __name__ == "__main__":
    main()
