#!/usr/bin/env python3
"""Reproduce the report's finite evidence without network access.

Default: verify pinned inputs, run both formula suites, compare exact examples,
and run the conservative auditor's regression suite.  --windows reruns the
radius-6 and radius-7 searches; --runtime reruns the symbolic runtime audit and
the literal billion-move diagnostic.  No Coq or Lean build is invoked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

if not __debug__:
    raise RuntimeError("Use Python with assertions enabled, without -O or -OO.")

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "build" / "reproduction"


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def verify_inputs() -> None:
    records = read_json(ROOT / "PROVENANCE.json")["source_files"]
    records = [(ROOT, item) for item in records]
    nested = ROOT / "machine_experiments"
    records += [(nested, item) for item in read_json(nested / "PROVENANCE.json")["sources"]]
    for base, item in records:
        actual = hashlib.sha256((base / item["file"]).read_bytes()).hexdigest()
        require(actual == item["sha256"], f"Source hash mismatch: {item['file']}")
    print(f"PASS: {len(records)} pinned source/data copies", flush=True)


def verify_manifest() -> None:
    path = ROOT / "MANIFEST.sha256"
    require(path.is_file(), "MANIFEST.sha256 is missing")
    count = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        digest, relative = line.split("  ", 1)
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        require(actual == digest, f"Archive manifest mismatch: {relative}")
        count += 1
    print(f"PASS: archive integrity ({count} files)", flush=True)


def run_json(label: str, command: list[str], *, cwd: Path = ROOT,
             result_name: str | None = None):
    print(f"Running {label} ...", flush=True)
    result = subprocess.run(command, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(f"{label} failed ({result.returncode})\n{result.stdout}\n{result.stderr}")
    parsed = json.loads(result.stdout)
    if result_name:
        (BUILD / result_name).write_text(json.dumps(parsed, indent=2) + "\n", encoding="utf-8")
    if result.stderr:
        (BUILD / (result_name or label.replace(" ", "_") + ".json")).with_suffix(".log").write_text(result.stderr)
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-only", action="store_true", help="check source and complete archive hashes only")
    parser.add_argument("--windows", action="store_true", help="rerun both larger local-window searches")
    parser.add_argument("--runtime", action="store_true", help="rerun runtime cases and the billion-move diagnostic")
    parser.add_argument("--all", action="store_true", help="run all checks")
    args = parser.parse_args()
    verify_inputs()
    if args.verify_only:
        verify_manifest()
        return
    BUILD.mkdir(parents=True, exist_ok=True)
    for schema, example in (("epsc", "fused_example.json"), ("gic", "gic_fused_example.json")):
        example_out = BUILD / example
        result = run_json(schema.upper() + " formula suite",
                          [sys.executable, str(ROOT / "code" / f"{schema}_fusion.py"),
                           "--example", str(example_out)], result_name=f"{schema}_fusion_evidence.json")
        require(result == read_json(ROOT / "evidence" / f"{schema}_fusion_evidence.json"),
                f"{schema} regression evidence changed")
        require(read_json(example_out) == read_json(ROOT / "evidence" / example),
                f"{schema} exact formula example changed")
        print(f"PASS: {schema.upper()} evidence and exact formulas match", flush=True)
    tests = run_json("auditor regressions", [sys.executable, str(ROOT / "code" / "audit_tm.py"), "--self-test"])
    require(tests == {"self_tests_passed": 11}, "Auditor self-test result changed")
    print("PASS: 11 auditor regressions", flush=True)
    if args.windows or args.all:
        for radius in (6, 7):
            result = run_json(f"radius-{radius}, 512-step local-window search",
                              [sys.executable, str(ROOT / "code" / "audit_tm.py"),
                               str(ROOT / "machines" / "zfc_253.tm"),
                               "--expected-sha256", "84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95",
                               "--expected-states", "253", "--expected-halt", "253",
                               "--window-radius", str(radius), "--macro-steps", "512",
                               "--source-commit", "0d544f2a2e3c18f12278441a74b7879f31cbe856",
                               "--source-url", "https://github.com/mira-emmy/busy-beaver/tree/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253"],
                              result_name=f"radius{radius}_steps512.json")
            recorded = read_json(ROOT / "evidence" / f"radius{radius}_steps512.json")
            for key in ("local_window_macro_search", "state_graph", "step_bisimulation", "startup_reuse", "model"):
                require(result[key] == recorded[key], f"radius-{radius} result changed: {key}")
            print(f"PASS: radius-{radius} search matches recorded evidence", flush=True)
    if args.runtime or args.all:
        directory = ROOT / "machine_experiments"
        result = run_json("all fixed and affine runtime branches",
                          [sys.executable, str(directory / "fixed_gap_audit.py")], cwd=directory,
                          result_name="fixed_gap_results.json")
        require(result == read_json(directory / "results" / "fixed_gap_results.json"), "Runtime branch evidence changed")
        print("PASS: all 25,173 symbolic cases match", flush=True)
        compiler = shutil.which("g++") or shutil.which("clang++")
        require(compiler is not None, "A C++17 compiler (g++ or clang++) is required for --runtime")
        executable = BUILD / "bootstrap_extension"
        print("Compiling literal simulator ...", flush=True)
        subprocess.run([compiler, "-O3", "-std=c++17", "-Wall", "-Wextra", "-pedantic",
                        str(directory / "bootstrap_extension.cpp"), "-o", str(executable)], check=True)
        result = run_json("one billion literal moves",
                          [str(executable), str(directory / "sources" / "zfc_254.tm"),
                           str(directory / "results" / "pc_words_34.txt"), "1000000000", "36"],
                          result_name="bootstrap_1e9_gap36.json")
        require(result == read_json(directory / "results" / "bootstrap_1e9_gap36.json"), "Literal bootstrap evidence changed")
        print("PASS: literal billion-move diagnostic matches", flush=True)
    print("All requested finite checks passed. No sub-253 correctness theorem or proof-assistant build is claimed.", flush=True)


if __name__ == "__main__":
    main()
