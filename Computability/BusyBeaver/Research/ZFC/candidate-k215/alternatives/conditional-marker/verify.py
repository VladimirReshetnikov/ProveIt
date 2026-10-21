#!/usr/bin/env python3
"""Portable reconstruction and independent audits of the CM215 research packet.

Python 3.10+; standard library only. Assertions must remain enabled.
The default audits saved universal evidence, but does not rederive that proof.
Use --runtime /fresh/directory to rerun the complete quantified checker.
The ordinary mathematical arguments and inherited calibration are in report.pdf.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
NATIVE = "e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252"
DENSE = "1f4f084f7293e2b042d5746039f793ff72ed429083b504970c939a5515e666cf"
SOURCE = "17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def require(condition: bool, message: str):
    if not condition:
        raise RuntimeError(message)


def main():
    require(__debug__, "Run Python with assertions enabled; do not use -O.")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--runtime", type=Path,
                    help="Rederive all quantified cases in this new/empty directory.")
    ap.add_argument("--output", type=Path,
                    help="Also save this run's final JSON receipt at the given path.")
    args = ap.parse_args()
    started = time.monotonic()
    results = []

    manifest = read(ROOT / "manifest.json")
    for entry in manifest["files"]:
        p = ROOT / entry["path"]
        require(p.is_file(), "Missing manifest file: " + entry["path"])
        require(p.stat().st_size == entry["size_bytes"] and sha(p) == entry["sha256"],
                "Manifest mismatch: " + entry["path"])
    results.append({"check": "complete_manifest", "files": len(manifest["files"])})
    print(f"PASS manifest: {len(manifest['files'])} files", flush=True)

    machine = ROOT / "machine"
    code = ROOT / "code"
    audit = ROOT / "evidence/audit"
    stride = ROOT / "research/stride2"
    require(sha(machine / "marker215.native.tm") == NATIVE, "Native machine pin")
    require(sha(machine / "marker215.tm") == DENSE, "Dense machine pin")
    require(sha(machine / "sites.json") == SOURCE, "Source pin")

    def check_runtime(folder: Path):
        r = read(folder / "runtime.json")
        require(r["status"] == "UNIVERSAL_MATHEMATICAL_PASS", "Universal runtime status")
        require(r["expected_cases"] == r["proved_cases"] == 6176, "Universal case count")
        require(r["working_states"] == 215 and r["site_count"] == 4751, "Universal source/state count")
        require(not r["failures"], "Universal runtime contains failures")
        require(r["table_sha256"] == NATIVE and r["sites_sha256"] == SOURCE, "Universal input pins")
        require(r["checker_sha256"] == sha(code / "runtime-inputs/runtime/symbolic_runtime.py"),
                "Universal checker pin")
        require(r["helper_sha256"] == sha(code / "runtime-inputs/runtime/independent_runtime.py"),
                "Universal helper pin")
        require(r["startup_status"] == "CALIBRATED_DIRTY_ROOT_SEED", "Startup status")
        return r

    check_runtime(machine / "runtime")
    results.append({"check": "saved_universal_report_and_code_pins", "proved_cases": 6176})

    with tempfile.TemporaryDirectory(prefix="cm215-verify-") as name:
        work = Path(name)

        def run(label, script, *arguments):
            command = [sys.executable, "-B", str(script), *map(str, arguments)]
            done = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT, check=False)
            require(done.returncode == 0,
                    label + " failed:\n" + done.stdout[-18000:])
            results.append({"check": label, "status": "PASS"})
            print("PASS " + label, flush=True)
            return done.stdout

        rebuilt = work / "machine"
        run("deterministic_machine_reconstruction", code / "build_marker215.py",
            "--base", ROOT / "reference/primary215", "--out", rebuilt)
        for name in ("marker215.native.tm", "marker215.tm", "sites.json",
                     "canonicalization.json", "construction.json"):
            require((rebuilt / name).read_bytes() == (machine / name).read_bytes(),
                    "Reconstruction differs: " + name)
        shutil.copytree(machine / "runtime", rebuilt / "runtime")
        run("literal_marker_hypotheses_prefixes_and_blank_replays", code / "check_marker215.py",
            "--base", ROOT / "reference/primary215", "--candidate", rebuilt)

        independent = work / "independent.json"
        run("independent_saved_case_audit_and_whole_blank_replay", audit / "audit_marker_evidence.py",
            "--candidate", machine, "--baseline", audit / "baseline",
            "--mapping", audit / "baseline/legacy_mapping.json", "--output", independent)
        r = read(independent)
        require(r["ordered_guard_cases"] == 6176 and r["exact_covered_rows"] == 430,
                "Independent inventory count")
        require(r["symbolic_rules"] == 1701542 and r["minimum_duration_constant"] == 6,
                "Independent runtime metrics")
        require(r["parent_constant_differences"] == {"0": 5632, "2": 128, "6": 416},
                "Independent parent duration delta")

        novelty = work / "novelty.json"
        run("rooted_and_reflected_graph_comparison", audit / "compare_tables.py",
            "--candidate", machine / "marker215.native.tm",
            "--roots", audit / "novelty_tables", "--output", novelty)
        n = read(novelty)
        require(n["distinct_same_size_literal_tables"] == 77 and
                not n["identical_rooted"] and not n["identical_reflected"] and
                not n["unsupported_files"], "Novelty inventory or comparison mismatch")

        for direct in (False, True):
            suffix = "direct" if direct else "composite"
            extra = ["--direct"] if direct else []
            generated = work / ("stride2-" + suffix)
            run("stride2_" + suffix + "_source_construction", stride / "build_source.py",
                "--parent", stride / "inputs/mp0-transfer201.sites.json",
                "--out", generated, *extra)
            supplied = stride / "direct" if direct else stride
            prefix = "direct2" if direct else "stride2"
            for i in range(5):
                name = f"{prefix}-{i}.sites.json"
                require((generated / name).read_bytes() == (supplied / name).read_bytes(),
                        "Two-head source differs: " + name)
            interfaces = work / (suffix + "-interfaces.json")
            run("stride2_" + suffix + "_compiler_interfaces_and_finite_credit",
                stride / "check_stride2.py", "--output", interfaces, *extra)
            ir = read(interfaces)
            require(ir["interface_cases"] == 79 and ir["required_credit_at_N1"] == 2,
                    "Two-head interface count or credit")
            command_report = work / (suffix + "-command.json")
            run("stride2_" + suffix + "_literal_command_cases",
                stride / "check_source_command.py", "--source", generated / f"{prefix}-0.sites.json",
                "--output", command_report, *extra)
            cr = read(command_report)
            require(cr["cases"] == 81 and cr["exact_guard_halts"] == (45 if direct else 57),
                    "Two-head literal guard census")

        scratch = work / "scratch-return.json"
        run("archived_scratch_return_counterexample", audit / "check_scratch_return.py",
            "--packet", audit / "scratch_return_packet", "--output", scratch)
        sr = read(scratch)
        require(sr["return"]["target"] == 23 and sr["corrected_return"]["target"] == 0,
                "Scratch-return target")
        require(sr["witness_steps_to_CH"] == 15 and sr["whole_blank_prefix_steps"] == 69744,
                "Scratch-return witness counts")
        run("rejected214_complete_primitive_counterexample",
            ROOT / "research/rejected-return214/check_counterexample.py")
        run("saved_source_packing_word_and_complete_control_flow",
            ROOT / "research/source-packing/check_saved.py")

    if args.runtime is not None:
        runtime = args.runtime.expanduser().resolve()
        require(not runtime.exists() or (runtime.is_dir() and not any(runtime.iterdir())),
                "--runtime must name a new or empty directory")
        runtime.mkdir(parents=True, exist_ok=True)
        command = [sys.executable, "-B", str(code / "runtime-inputs/validate_native.py"),
                   str(machine / "marker215.native.tm"), str(machine / "sites.json"), str(runtime)]
        print("Rederiving the full quantified runtime; this may take several minutes.", flush=True)
        with (runtime / "execution.log").open("w") as log:
            completed = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        require(completed.returncode == 0, "Runtime process failed; inspect execution.log")
        check_runtime(runtime)
        results.append({"check": "fresh_universal_runtime", "status": "PASS", "proved_cases": 6176})
        print("PASS fresh_universal_runtime: 6176/6176", flush=True)

    result = {
        "status": "CM215_REPRODUCTION_PASS",
        "native_sha256": NATIVE, "dense_sha256": DENSE, "source_sha256": SOURCE,
        "checks": results, "fresh_runtime_requested": args.runtime is not None,
        "seconds": round(time.monotonic() - started, 3),
        "scope": ("Exact reconstruction, literal finite hypotheses, independent stored-case and "
                  "blank audits, new source construction, finite compiler corroborations, and "
                  "negative examples. Ordinary proofs and inherited calibration are separate. "
                  "The infinite credit theorem is in the report; finite credit checks are corroboration. "
                  "Fresh universal induction is rerun only with --runtime. No Lean/Rocq kernel claim.")
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
