#!/usr/bin/env python3
"""Verify the delivered 245-state construction and independent composition gates.

The optional --whole-frame proof expands arbitrary registers (several minutes).
The optional --literal regression regenerates 8385 fixtures and requires C++17.
All generated files are written outside the frozen certificate directories.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise RuntimeError("Assertions are required; do not use Python -O.")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--whole-frame", action="store_true")
    ap.add_argument("--literal", action="store_true")
    ap.add_argument("--output", type=Path, help="A new or empty directory for fresh results.")
    args = ap.parse_args()
    started = time.monotonic()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="zfc245-verification-"))
    if out.exists() and any(out.iterdir()):
        raise ValueError("The output directory must be empty; frozen results are never overwritten.")
    out.mkdir(parents=True, exist_ok=True)
    inventory = ROOT / "SHA256SUMS"
    checked = 0
    for line in inventory.read_text().splitlines():
        expected, rel = line.split("  ", 1)
        path = ROOT / rel
        assert path.is_relative_to(ROOT) and path.is_file(), rel
        assert digest(path) == expected, ("Artifact hash mismatch", rel)
        checked += 1
    print(f"PASS: {checked} delivered file hashes.", flush=True)

    env = os.environ.copy()
    env["PYTHONDONTWRITEBYTECODE"] = "1"

    def run(name, command):
        print(f"Checking {name} ...", flush=True)
        log = out / (name + ".log")
        with log.open("w") as stream:
            result = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"{name} failed:\n{log.read_text()[-8000:]}")
        print(f"PASS: {name}.", flush=True)

    py = [sys.executable, "-B"]
    core = py + [ROOT / "code/verify.py", "--output", out / "core"]
    if args.whole_frame:
        core.append("--whole-frame")
    run("core-runtime-and-source", core)
    run("printed-transition-table", py + [ROOT / "code/render_transition_table.py", "--check"])
    assert (ROOT / "machine/zfc245.tm").read_bytes() == (ROOT / "certificate/machine.tm").read_bytes()
    assert (ROOT / "machine/zfc245_old.tm").read_bytes() == (ROOT / "certificate/machine_old.tm").read_bytes()
    run("independent-frame-composition", py + [
        ROOT / "code/verify_machine_frame245.py", "--machine", out / "core/built",
        "--grammar", ROOT / "grammar.json", "--lock", ROOT / "inputs/state_reduction/bootstrap-lock54.txt",
        "--output", out / "frame-composition.json"])
    frame = json.loads((out / "frame-composition.json").read_text())
    assert frame["status"] == "PASS" and frame["nonhalting_successors_normalized"] == 8390
    assert frame["bootstrap_lock_immediate_projections_checked"] == 54
    run("independent-grammar", py + [
        ROOT / "code/state_reduction/check_route_grammar.py", ROOT / "grammar.json",
        "--inputs", ROOT / "reference/grammar", "--bootstrap-lock", ROOT / "inputs/state_reduction/bootstrap-lock54.txt",
        "--output", out / "grammar-audit.json"])
    run("scanner-contraction", py + [
        ROOT / "code/state_reduction/check_short_scan_boot.py",
        "--table", ROOT / "reference/tables/zfc_prefix246_old.tm",
        "--baseline-bootstrap", ROOT / "reference/bootstrap/bootstrap.json",
        "--output", out / "scanner-contraction.json"])
    scanner = json.loads((out / "scanner-contraction.json").read_text())
    assert scanner["contractions"] == 1410 and scanner["shortened_steps"] == 407915
    run("independent-blank-replay", py + [
        ROOT / "code/state_reduction/check_candidate_boot.py",
        "--table", out / "core/built/machine_old.tm", "--steps", "407915",
        "--baseline-bootstrap", ROOT / "reference/bootstrap/bootstrap.json",
        "--output", out / "independent-boot.json"])
    boot = json.loads((out / "independent-boot.json").read_text())
    assert boot["status"] == "PASS_EXACT_TWO_INTERPRETER_BOOT" and boot["one_count"] == 351

    literal = None
    if args.literal:
        compiler = shutil.which("g++") or shutil.which("clang++")
        if compiler is None:
            raise RuntimeError("--literal requires g++ or clang++ with C++17 support.")
        run("ordered-leaf-fixture-transfer", py + [
            ROOT / "code/state_reduction/transfer_instruction_metadata.py",
            "--program", ROOT / "reference/source/Prog254.v",
            "--sites", out / "core/built/sites_logical.json",
            "--metadata", ROOT / "reference/interval/instruction-metadata.json",
            "--output", out / "instruction-metadata.json"])
        run("literal-fixture-generation", py + [
            ROOT / "code/state_reduction/make_resource_merge_cases.py",
            "--metadata", out / "instruction-metadata.json",
            "--literal-helper", ROOT / "reference/literal/check_literal_instructions.py",
            "--table", out / "core/built/machine_old.tm", "--output", out / "literal-cases.txt"])
        frozen = gzip.decompress((ROOT / "inputs/state_reduction/candidate245-literal-cases.txt.gz").read_bytes())
        assert (out / "literal-cases.txt").read_bytes() == frozen, "Regenerated literal fixtures differ."
        run("literal-checker-compilation", [compiler, "-O3", "-std=c++17",
            ROOT / "code/state_reduction/check_literal_cases.cpp", "-o", out / "check_literal_cases"])
        run("independent-literal-cases", [out / "check_literal_cases", out / "literal-cases.txt"])
        literal = json.loads((out / "independent-literal-cases.log").read_text().splitlines()[-1])
        assert literal["status"] == "PASS_FINITE_LITERAL_CASES" and literal["cases"] == 8385
        assert literal["rows_exercised"] == 490

    result = dict(status="PASS_245_DELIVERY", working_states=245, binary_rows=490,
                  delivered_hashes_checked=checked,
                  core=json.loads((out / "core/verification.json").read_text()),
                  independent_residual_cases=8390, bootstrap_equations=54,
                  scanner_contractions=1410, independent_blank_steps=407915,
                  literal=literal, elapsed_seconds=round(time.monotonic() - started, 3),
                  output=str(out),
                  proof_status="Ordinary ZFC proof with executable certificates; no new kernel endpoint.")
    (out / "verification-summary.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
