#!/usr/bin/env python3
"""Replay Report214 finite results and deliberate failures in normal and -O Python.

Uses only the Python standard library. No network, TeX, or numerical fitting.
The destination must be a new directory outside the source tree.
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
SOURCE_ROOT = HERE.parent if HERE.name == "code" else HERE
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
            and not artifact.exists() and not artifact.is_symlink(), "negative_test", {
                "case": case, "optimized": optimized, "returncode": process.returncode,
                "intended_marker": marker, "stderr": process.stderr})
    results.append({"case": case, "optimized": optimized, "guard": marker,
                    "nonzero_exit": True, "intended_marker_observed": True,
                    "success_output_created": False})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--self-test-failure", action="store_true",
                        help="Deliberately fail before computation or output writes")
    args = parser.parse_args()
    require(not args.out.exists() and not args.out.is_symlink(), "output_exists", str(args.out))
    out = args.out.resolve()
    require(out != SOURCE_ROOT and SOURCE_ROOT not in out.parents and out not in SOURCE_ROOT.parents,
            "output_inside_source", str(out))
    require(out.parent.is_dir(), "output_parent", str(out.parent))
    require(not args.self_test_failure, "driver_prewrite", "Deliberate pre-write failure")
    require({p.name for p in HERE.glob("*.py")} == {name for name in SOURCE_FILES if name.endswith(".py")}
            and all((HERE / name).is_file() and not (HERE / name).is_symlink() for name in SOURCE_FILES),
            "source_inventory", "Expected exactly three Python source files and README")
    for name in SOURCE_FILES:
        if name.endswith(".py"):
            tree = ast.parse((HERE / name).read_text(encoding="utf-8"))
            require(not any(isinstance(node, ast.Assert) for node in ast.walk(tree)), "assertion_ast_scan", name)
    tests = []
    with tempfile.TemporaryDirectory(prefix=".report214-replay-", dir=out.parent) as temp:
        work = Path(temp)
        positive, stdout = [], []
        for optimized in (False, True):
            dest = work / ("optimized" if optimized else "normal")
            stdout.append(success(python_command(optimized) + [str(HERE / "finite_checks.py"),
                                  "--out", str(dest), "--compare", str(HERE / "results")]))
            positive.append(dest)
        require(stdout[0] == stdout[1], "optimization_stdout", "Normal and -O stdout differ")
        for name in RESULT_FILES:
            require((positive[0] / name).read_bytes() == (positive[1] / name).read_bytes(),
                    "optimization_results", name)
        for optimized in (False, True):
            python = python_command(optimized)
            for guard in MATH_GUARDS:
                dest = work / f"failure-{guard}-{optimized}"
                failure(python + [str(HERE / "finite_checks.py"), "--out", str(dest), "--inject-failure", guard],
                        guard, dest, tests, "mathematical-value-" + guard, optimized)
            mutations = ("checks_json_value", "polynomial_json_value", "checks_duplicate_key", "polynomial_duplicate_key",
                         "selected_csv_value", "table_tex_value", "rows_tex_value", "missing_file", "extra_file", "linked_file")
            for mutation in mutations:
                reference = work / f"reference-{mutation}-{optimized}"
                shutil.copytree(HERE / "results", reference)
                marker = "reference_comparison"
                if mutation in ("checks_json_value", "polynomial_json_value"):
                    name = "checks.json" if mutation == "checks_json_value" else "polynomials.json"
                    path = reference / name
                    value = json.loads(path.read_text(encoding="utf-8"))
                    if mutation == "checks_json_value":
                        value["enumerated_rows"][0]["a_k"] += 1
                    else:
                        value["polynomials"]["2"]["P_monomial_coefficients_ascending"][1]["numerator"] = "999"
                    path.write_bytes(json_bytes(value))
                elif mutation in ("checks_duplicate_key", "polynomial_duplicate_key"):
                    name = "checks.json" if mutation == "checks_duplicate_key" else "polynomials.json"
                    path = reference / name
                    path.write_text('{"schema":"deliberate-duplicate",' + path.read_text(encoding="utf-8")[1:], encoding="utf-8")
                    marker = "json_duplicate"
                elif mutation == "selected_csv_value":
                    path = reference / "selected_table.csv"
                    lines = path.read_text(encoding="utf-8").splitlines()
                    values = lines[1].split(",")
                    values[1] = str(int(values[1]) + 1)
                    lines[1] = ",".join(values)
                    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                elif mutation in ("table_tex_value", "rows_tex_value"):
                    path = reference / ("table.tex" if mutation == "table_tex_value" else "rows.tex")
                    path.write_bytes(path.read_bytes() + b"% Deliberate corruption\n")
                elif mutation == "missing_file":
                    (reference / "rows.tex").unlink()
                    marker = "reference_inventory"
                elif mutation == "extra_file":
                    (reference / "unexpected.txt").write_text("Deliberate extra file\n", encoding="utf-8")
                    marker = "reference_inventory"
                else:
                    (reference / "rows.tex").unlink()
                    (reference / "rows.tex").symlink_to(HERE / "results" / "rows.tex")
                    marker = "reference_inventory"
                dest = work / f"failure-{mutation}-{optimized}"
                failure(python + [str(HERE / "finite_checks.py"), "--out", str(dest), "--compare", str(reference)],
                        marker, dest, tests, mutation, optimized)
            altered_source = work / f"extra-source-{optimized}"
            altered_source.mkdir()
            for name in SOURCE_FILES:
                shutil.copy2(HERE / name, altered_source / name)
            shutil.copytree(HERE / "results", altered_source / "results")
            (altered_source / "unexpected.py").write_text("# Deliberate extra source\n", encoding="utf-8")
            dest = work / f"failure-source-inventory-{optimized}"
            failure(python + [str(altered_source / "reproduce.py"), "--out", str(dest)],
                    "source_inventory", dest, tests, "extra_source_file", optimized)
            dest = work / f"failure-driver-{optimized}"
            failure(python + [str(HERE / "reproduce.py"), "--out", str(dest), "--self-test-failure"],
                    "driver_prewrite", dest, tests, "driver_prewrite", optimized)
            for script in ("reproduce.py", "finite_checks.py"):
                label = script.removesuffix(".py")
                dest = work / f"missing-parent-{label}-{optimized}" / "child"
                failure(python + [str(HERE / script), "--out", str(dest)], "output_parent", dest, tests,
                        f"{label}_missing_parent", optimized)
                dest = HERE / f"forbidden-{label}-{optimized}"
                require(not dest.exists() and not dest.is_symlink(), "negative_test_setup", str(dest))
                failure(python + [str(HERE / script), "--out", str(dest)], "output_inside_source", dest, tests,
                        f"{label}_source_output_refused", optimized)
                for kind in ("directory", "file", "dangling_symlink"):
                    dest = work / f"existing-{label}-{kind}-{optimized}"
                    if kind == "directory":
                        dest.mkdir()
                        (dest / "sentinel.txt").write_bytes(b"must remain unchanged\n")
                        before = {p.name: p.read_bytes() for p in dest.iterdir()}
                    elif kind == "file":
                        dest.write_bytes(b"must remain unchanged\n")
                        before = dest.read_bytes()
                    else:
                        dest.symlink_to(work / "nonexistent-target")
                        before = dest.readlink()
                    process = subprocess.run(python + [str(HERE / script), "--out", str(dest)],
                                             capture_output=True, text=True, check=False)
                    after = ({p.name: p.read_bytes() for p in dest.iterdir()} if kind == "directory"
                             else dest.read_bytes() if kind == "file" else dest.readlink())
                    require(process.returncode != 0 and "CHECK_FAILED[output_exists]" in process.stderr
                            and before == after, "negative_test", (script, kind, "existing output changed or accepted"))
                    tests.append({"case": f"{label}_existing_{kind}_preserved", "optimized": optimized,
                                  "guard": "output_exists", "nonzero_exit": True,
                                  "intended_marker_observed": True, "existing_bytes_or_link_unchanged": True})
        guard_receipt = {
            "all_checks_passed": True, "assertion_ast_scan_passed": True,
            "normal_optimized_result_bytes_identical": True, "normal_optimized_stdout_bytes_identical": True,
            "negative_tests_passed": len(tests), "tests": tests,
            "limits": "Selected deliberate mathematical comparison failures and documented validation/output-safety cases only. This is not a proof of complete fault detection, a hostile-filesystem security audit, or mathematical asymptotics.",
        }
        receipt = {
            "schema": "Report214.finite-reproduction.v1", "all_checks_passed": True,
            "fresh_recurrence_max_k": 32, "independent_enumeration_max_k": 7,
            "source_sha256": {name: sha256((HERE / name).read_bytes()) for name in SOURCE_FILES},
            "result_sha256": {name: sha256((positive[0] / name).read_bytes()) for name in RESULT_FILES},
            "guards_sha256": sha256(json_bytes(guard_receipt)), "negative_tests_passed": len(tests),
            "scope": "Standard-library finite replay only. PDF and ZIP reconstruction belong to the outer package driver. No finite check establishes an asymptotic estimate, effective onset, or inverse enclosure radius.",
        }
        # No success destination is created until every positive and negative check passes.
        out.mkdir()
        shutil.copytree(positive[0], out / "results")
        (out / "guard_checks.json").write_bytes(json_bytes(guard_receipt))
        (out / "reproduction.json").write_bytes(json_bytes(receipt))
    print(json_bytes(receipt).decode(), end="")


if __name__ == "__main__":
    main()
