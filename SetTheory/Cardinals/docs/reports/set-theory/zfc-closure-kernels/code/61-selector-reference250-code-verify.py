#!/usr/bin/env python3
"""Verify the assembled prefix250 research package using only Python's stdlib.

Run from the package root with ``python -B code/verify.py``. Paths are resolved
relative to this file, so the same command also works from any other directory
when an absolute path to this entry point is supplied. The two pairs of literal
regression scripts in code/ are alternatives; this entry point runs one pair.

This is reproducible mathematical and computational evidence, not a fresh
Lean/Rocq endpoint or a runtime test of nonhalting.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Assertions are required: do not run this verifier with Python -O or -OO.")

from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
SUMMARY = RESULTS / "verification-summary.json"


def metrics(name, data):
    """Keep the console and combined certificate compact; retain full per-check JSON."""
    if name == "exact_reconstruction":
        return {k: data[k] for k in ("working_states", "binary_rows", "source_tree_nodes",
            "instruction_sites", "guarded_instruction_cases", "final_old_sha256", "final_canonical_sha256")}
    if name == "macro_inductions":
        return dict(block_theorems=len(data["block_theorems"]),
            macro_theorems=len(data["macro_theorems"]), marking_theorems=len(data["mark_theorems"]),
            unbounded_register_parameters=True,
            macro_steps={row["name"]: row["steps"] for row in data["macro_theorems"]})
    if name == "guarded_instructions":
        return {k: data[k] for k in ("cases", "source_rows", "instruction_sites",
            "minimum_literal_steps_per_case", "max_rules_per_case")}
    if name == "independent_marking":
        return dict(unchanged_footprint_rows=len(data["footprint"]),
            symbolic_physical_positions=len(data["start_states"]),
            duration=data["duration"], finite_sampling_used_for_unbounded_claim=False)
    if name == "full_source_and_full_pc":
        recheck = data["universal_guarded_recheck"]
        return dict(source_nodes=data["node_count"], source_leaves=data["source_site_count"],
            fully_consumed_source_tokens=data["fully_consumed_source_tokens"],
            oracle_guard_checks=data["oracle_guard_checks"],
            guarded_cases=recheck["cases"],
            full_target_pc_preserved=recheck["target_paths_keep_all_overflow_and_trailing_zero_cells"],
            site_numbering="physical", site_source="sources/prior/instruction-sites-physical.json")
    if name == "pulse_and_dual_bootstrap":
        return {k: data[k] for k in ("bootstrap_steps", "dual_sparse_dense_agreement", "gap",
            "logical_primary", "spare_count", "one_count", "all_other_cells_zero")}
    if name == "independent_retiming":
        boot = data["bootstrap"]
        return dict(local_cases=len(data["local_cases"]), blank_steps=boot["actual_blank_steps"],
            compared_cutpoints=boot["compared_cutpoints"],
            complete_tapes_equal_at_every_cutpoint=boot["complete_tapes_equal_at_every_cutpoint"],
            postinitial_core_steps=boot["postinitial_core_steps"])
    if name == "literal_instructions":
        return {k: data[k] for k in ("cases", "literal_steps", "maximum_case_steps",
            "transition_pairs_used", "finite_only", "unbounded_proof")}
    if name == "literal_macros":
        return {k: data[k] for k in ("total_cases", "literal_steps", "counts", "finite_only", "unbounded_proof")}
    raise AssertionError(name)


CHECKS = [
    ("exact_reconstruction", ["code/rebuild_machines.py", "--check"], "results/rebuild.json", True),
    ("macro_inductions", ["code/check_macro_inductions.py"], "results/macro-inductions.json", False),
    ("guarded_instructions", ["code/check_instructions.py"], "results/instructions.json", False),
    ("independent_marking", ["code/audit_marking_transport.py",
        "--baseline", "sources/baseline252_old.tm", "--candidate", "machine/zfc_prefix250_old.tm",
        "--output", "results/marking-transport.json"], "results/marking-transport.json", False),
    ("full_source_and_full_pc", ["code/review_affine_source.py",
        "--program", "sources/Prog254.v",
        # This checker outputs physical register indices. The generated file
        # results/instruction-sites.json instead uses logical register indices.
        "--sites", "sources/prior/instruction-sites-physical.json",
        "--table", "machine/zfc_prefix250_old.tm", "--checker", "code/affine_engine.py",
        "--output", "results/affine-source-review.json"], "results/affine-source-review.json", False),
    ("pulse_and_dual_bootstrap", ["code/check_pulse_boot.py"], "results/pulse-bootstrap.json", False),
    ("independent_retiming", ["code/verify_retiming_independent.py",
        "--table", "machine/zfc_prefix250_old.tm", "--output", "results/retiming-independent.json"],
        "results/retiming-independent.json", False),
    ("literal_instructions", ["code/check_literal_instructions.py",
        "--baseline", "sources/baseline252_old.tm", "--program", "sources/Prog254.v",
        "--table", "machine/zfc_prefix250_old.tm", "--output", "results/literal-instructions.json"],
        "results/literal-instructions.json", False),
    ("literal_macros", ["code/check_literal_macros.py",
        "--table", "machine/zfc_prefix250_old.tm", "--output", "results/literal-macros.json"],
        "results/literal-macros.json", False),
]


def main():
    RESULTS.mkdir(exist_ok=True)
    began = time.monotonic()
    results = []
    summary = dict(status="RUNNING", started_utc=datetime.now(timezone.utc).isoformat(),
        python_version=platform.python_version(), assertions_enabled=__debug__,
        entry_point="python -B code/verify.py", expected_check_count=len(CHECKS), checks=results,
        scope="Packaged reconstruction, universal induction templates, independent symbolic audits, exact finite bootstraps, and secondary literal regressions.",
        proof_assistant_kernel_rebuilt=False, logical_calibration_kernel_rebuilt=False,
        nonhalting_inferred_from_finite_execution=False)
    env = os.environ.copy()
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    failed = None
    for name, arguments, result_file, result_from_stdout in CHECKS:
        started = time.monotonic()
        command = [sys.executable, "-B", *arguments]
        record = dict(name=name, command=["python", "-B", *arguments], result_file=result_file)
        try:
            completed = subprocess.run(command, cwd=ROOT, env=env,
                capture_output=True, text=True, check=False)
            record["exit_code"] = completed.returncode
            if completed.returncode != 0:
                raise RuntimeError((completed.stderr or completed.stdout)[-6000:].strip())
            if result_from_stdout:
                data = json.loads(completed.stdout)
                # rebuild --check prints a fresh result without modifying the
                # generated tables. Record that fresh certificate in results/.
                (ROOT / result_file).write_text(json.dumps(data, indent=2)+"\n", encoding="ascii")
            else:
                data = json.loads((ROOT / result_file).read_text(encoding="utf-8"))
            assert data.get("status") == "PASS", (name, data.get("status"))
            record.update(status="PASS", seconds=round(time.monotonic()-started, 6),
                metrics=metrics(name, data),
                result_sha256=sha256((ROOT / result_file).read_bytes()).hexdigest(),
                script_sha256=sha256((ROOT / arguments[0]).read_bytes()).hexdigest())
            print(f"PASS {name}: {record['seconds']:.3f}s -> {result_file}", flush=True)
        except Exception as error:
            record.update(status="FAIL", seconds=round(time.monotonic()-started, 6), error=str(error))
            failed = record
            print(f"FAIL {name}: {error}", file=sys.stderr, flush=True)
        results.append(record)
        if failed is not None:
            break
    summary.update(status="FAIL" if failed else "PASS",
        finished_utc=datetime.now(timezone.utc).isoformat(),
        total_seconds=round(time.monotonic()-began, 6),
        completed_check_count=len(results), passed_check_count=sum(r["status"] == "PASS" for r in results),
        packaged_input_hashes={name: sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ("sources/baseline252_old.tm", "sources/Prog254.v",
                "sources/prior/instruction-sites-physical.json", "machine/zfc_prefix250_old.tm",
                "machine/zfc_prefix250.tm", "machine/renumbering.json", "code/affine_engine.py")})
    SUMMARY.write_text(json.dumps(summary, indent=2)+"\n", encoding="utf-8")
    if failed:
        raise SystemExit(1)
    print(f"PASS all {len(CHECKS)} checks in {summary['total_seconds']:.3f}s; results/verification-summary.json", flush=True)


if __name__ == "__main__":
    main()
