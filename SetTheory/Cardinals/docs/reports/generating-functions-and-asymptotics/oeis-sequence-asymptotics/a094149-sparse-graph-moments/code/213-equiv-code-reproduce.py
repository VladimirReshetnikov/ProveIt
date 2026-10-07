#!/usr/bin/env python3
"""Reproduce Report213 finite results and exercise guards in normal and -O Python.

No downloads, third-party libraries, compilers, TeX, or stored recurrence inputs.
The output directory must be new and outside this source package.
"""
import argparse
import ast
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
from common import RESULT_FILES, json_bytes, require, sha256
from finite_checks import MATH_GUARDS

HERE = Path(__file__).resolve().parent
SOURCE_FILES = ("common.py", "finite_checks.py", "reproduce.py", "README.md")


def python_command(optimized):
    return [sys.executable, "-B"] + (["-O"] if optimized else [])


def success(command):
    process = subprocess.run(command, capture_output=True, text=True, check=False)
    require(process.returncode == 0, "subprocess_success", process.stderr)
    return process.stdout.encode("utf-8")


def failure(command, marker, artifact, results, case, optimized):
    process = subprocess.run(command, capture_output=True, text=True, check=False)
    require(process.returncode != 0 and f"CHECK_FAILED[{marker}]" in process.stderr
            and not artifact.exists(), "negative_test", {
                "case": case, "optimized": optimized, "returncode": process.returncode,
                "intended_marker": marker, "output_exists": artifact.exists(),
                "stderr": process.stderr,
            })
    results.append({"case": case, "optimized": optimized, "guard": marker,
                    "nonzero_exit": True, "intended_marker_observed": True,
                    "success_output_created": False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--self-test-failure", action="store_true",
                        help="Deliberately fail a pre-write guard; used by the negative harness.")
    args = parser.parse_args()
    out = args.out.resolve()
    require(not out.exists(), "output_exists", str(out))
    require(out.parent.is_dir(), "output_parent", str(out.parent))
    require(out != HERE and HERE not in out.parents, "output_inside_source", str(out))
    require(not args.self_test_failure, "driver_prewrite", "Deliberate driver guard test")
    require({p.name for p in HERE.glob("*.py")} == {name for name in SOURCE_FILES if name.endswith(".py")}
            and all((HERE / name).is_file() for name in SOURCE_FILES),
            "source_inventory", "Expected exactly the three documented Python source files and README")
    for source in sorted(HERE.glob("*.py")):
        syntax = ast.parse(source.read_text(encoding="utf-8"))
        require(not any(isinstance(node, ast.Assert) for node in ast.walk(syntax)),
                "assertion_ast_scan", source.name)
    tests = []
    with tempfile.TemporaryDirectory(prefix=".report213-replay-", dir=out.parent) as temp:
        work = Path(temp)
        positive = []
        stdout = []
        for optimized in (False, True):
            dest = work / ("optimized" if optimized else "normal")
            stdout.append(success(python_command(optimized) + [str(HERE / "finite_checks.py"),
                                  "--out", str(dest), "--compare", str(HERE / "results")]))
            positive.append(dest)
        require(stdout[0] == stdout[1], "optimization_stdout", "Normal and -O stdout must match bytes")
        for name in RESULT_FILES:
            require((positive[0] / name).read_bytes() == (positive[1] / name).read_bytes(),
                    "optimization_results", name)
        for optimized in (False, True):
            python = python_command(optimized)
            for guard in MATH_GUARDS:
                dest = work / f"failure-{guard}-{optimized}"
                failure(python + [str(HERE / "finite_checks.py"), "--out", str(dest),
                                 "--inject-failure", guard], guard, dest, tests,
                        f"mathematical-value-{guard}", optimized)
            # These mutate actual serialized reference bytes, not a verifier return.
            mutations = ("json_value", "duplicate_json_key", "moment_csv_value",
                         "selected_csv_value", "tex_value", "missing_file", "extra_file")
            for mutation in mutations:
                reference = work / f"reference-{mutation}-{optimized}"
                shutil.copytree(HERE / "results", reference)
                marker = "reference_comparison"
                if mutation == "json_value":
                    path = reference / "checks.json"
                    value = json.loads(path.read_text(encoding="utf-8"))
                    value["enumerated_rows"][0]["a_k"] += 1
                    path.write_bytes(json_bytes(value))
                elif mutation == "duplicate_json_key":
                    path = reference / "checks.json"
                    raw = path.read_text(encoding="utf-8")
                    path.write_text('{"schema":"deliberate-duplicate",' + raw[1:], encoding="utf-8")
                    marker = "json_duplicate"
                elif mutation in ("moment_csv_value", "selected_csv_value"):
                    path = reference / ("moments.csv" if mutation == "moment_csv_value" else "selected_table.csv")
                    lines = path.read_text(encoding="utf-8").splitlines()
                    values = lines[1].split(",")
                    values[1] = str(int(values[1]) + 1)
                    lines[1] = ",".join(values)
                    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                elif mutation == "tex_value":
                    path = reference / "table.tex"
                    path.write_bytes(path.read_bytes() + b"% deliberately corrupted\n")
                elif mutation == "missing_file":
                    (reference / "moments.csv").unlink()
                    marker = "reference_inventory"
                else:
                    (reference / "unexpected.txt").write_text("deliberate extra file\n", encoding="utf-8")
                    marker = "reference_inventory"
                dest = work / f"failure-{mutation}-{optimized}"
                failure(python + [str(HERE / "finite_checks.py"), "--out", str(dest),
                                 "--compare", str(reference)], marker, dest, tests, mutation, optimized)
            # An actual unexpected source file must be rejected before replay.
            altered_source = work / f"extra-source-{optimized}"
            altered_source.mkdir()
            for name in SOURCE_FILES:
                shutil.copy2(HERE / name, altered_source / name)
            shutil.copytree(HERE / "results", altered_source / "results")
            (altered_source / "unexpected.py").write_text("# Deliberate source-inventory corruption\n", encoding="utf-8")
            dest = work / f"failure-source-inventory-{optimized}"
            failure(python + [str(altered_source / "reproduce.py"), "--out", str(dest)],
                    "source_inventory", dest, tests, "extra_source_file", optimized)
            # Deliberate failures of the outer driver's pre-write path checks.
            dest = work / f"failure-driver-{optimized}"
            failure(python + [str(HERE / "reproduce.py"), "--out", str(dest), "--self-test-failure"],
                    "driver_prewrite", dest, tests, "driver_prewrite", optimized)
            dest = work / f"nonexistent-parent-{optimized}" / "child"
            failure(python + [str(HERE / "reproduce.py"), "--out", str(dest)],
                    "output_parent", dest, tests, "missing_output_parent", optimized)
            dest = HERE / f"forbidden-replay-{optimized}"
            require(not dest.exists(), "negative_test_setup", str(dest))
            failure(python + [str(HERE / "reproduce.py"), "--out", str(dest)],
                    "output_inside_source", dest, tests, "source_output_refused", optimized)
            # An existing directory is never modified: compare its complete tree.
            dest = work / f"existing-output-{optimized}"
            dest.mkdir()
            (dest / "sentinel.txt").write_bytes(b"must remain unchanged\n")
            before = {p.name: p.read_bytes() for p in dest.iterdir()}
            process = subprocess.run(python + [str(HERE / "reproduce.py"), "--out", str(dest)],
                                     capture_output=True, text=True, check=False)
            after = {p.name: p.read_bytes() for p in dest.iterdir()}
            require(process.returncode != 0 and "CHECK_FAILED[output_exists]" in process.stderr
                    and before == after, "negative_test", "Existing output changed or not rejected")
            tests.append({"case": "existing_output_preserved", "optimized": optimized,
                          "guard": "output_exists", "nonzero_exit": True,
                          "intended_marker_observed": True, "existing_bytes_unchanged": True})
        guard_receipt = {"all_checks_passed": True, "assertion_ast_scan_passed": True,
                         "normal_optimized_result_bytes_identical": True,
                         "normal_optimized_stdout_bytes_identical": True,
                         "negative_tests_passed": len(tests), "tests": tests}
        result_hashes = {name: sha256((positive[0] / name).read_bytes()) for name in RESULT_FILES}
        receipt = {"schema": "Report213.finite-reproduction.v1", "all_checks_passed": True,
                   "fresh_recurrence_max_k": 32, "independent_enumeration_max_k": 8,
                   "source_sha256": {name: sha256((HERE / name).read_bytes()) for name in SOURCE_FILES},
                   "result_sha256": result_hashes,
                   "guards_sha256": sha256(json_bytes(guard_receipt)),
                   "negative_tests_passed": len(tests),
                   "scope": "Only the standard-library finite package is replayed here. The article's PDF and whole archive are handled separately. No finite check establishes an asymptotic estimate."}
        # Success is committed only after all checks, including negative tests.
        out.mkdir()
        shutil.copytree(positive[0], out / "results")
        (out / "guard_checks.json").write_bytes(json_bytes(guard_receipt))
        (out / "reproduction.json").write_bytes(json_bytes(receipt))
    print(json_bytes(receipt).decode("utf-8"), end="")


if __name__ == "__main__":
    main()
