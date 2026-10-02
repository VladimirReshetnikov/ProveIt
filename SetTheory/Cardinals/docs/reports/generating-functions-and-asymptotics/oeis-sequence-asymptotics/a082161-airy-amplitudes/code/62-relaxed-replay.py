#!/usr/bin/env python3
"""Verify all package inputs, replay every advertised check, and record results.

No downloads, installations, network calls, or files outside --output-dir.
SHA256SUMS detects input changes; it is not a signature/authenticity guarantee.
"""
import argparse
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
REQUIRED = {"README.md", "requirements.txt", "replay.py", "make_manifest.py",
            "coefficients.py", "exact_recurrence.py", "frozen_quasimode.py",
            "inverse_checks.py", "forward_evidence.py", "fixtures/expected.json"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_manifest(manifest):
    expected = {}
    for line in manifest.read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        sha, name = line.split("  ", 1)
        path = Path(name)
        if (len(sha) != 64 or any(c not in "0123456789abcdef" for c in sha)
                or path.is_absolute() or ".." in path.parts or name in expected):
            raise ValueError(f"Invalid manifest entry: {line}")
        expected[name] = sha
    if not REQUIRED <= expected.keys():
        raise ValueError(f"Manifest omits required inputs: {sorted(REQUIRED-expected.keys())}")
    actual = {}
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if relative.parts[0] == "output" or "__pycache__" in relative.parts:
            continue
        if path == manifest:
            continue
        if path.is_symlink():
            raise ValueError(f"Symlink input forbidden: {relative}")
        if path.is_dir():
            continue
        actual[relative.as_posix()] = path
    if set(actual) != set(expected):
        raise ValueError(f"Manifest inventory mismatch; unlisted={sorted(set(actual)-set(expected))}; missing={sorted(set(expected)-set(actual))}")
    for name, path in actual.items():
        if digest(path) != expected[name]:
            raise ValueError(f"SHA256 mismatch: {name}")
    return {"files_verified": len(expected), "manifest_sha256": digest(manifest)}


def check_fixture(name, result, fixture):
    if result.get("passed") is not True:
        raise AssertionError(f"{name} did not report passed=true")
    if name == "exact_recurrence":
        prefix = fixture["sequence_prefix"]
        assert result["sequence_first_15"][:len(prefix)] == prefix
    elif name == "coefficients":
        import sympy as S
        for group in ("s", "forward_log_n", "forward_relative_n"):
            for key, value in fixture[group].items():
                if key in result[group]:
                    assert S.expand(S.sympify(result[group][key])-S.sympify(value)) == 0, (group,key)
    elif name == "frozen_quasimode":
        assert result["frozen_residual_eps0_through_eps5"] == "exactly zero"
        assert result["boundary"] == "exactly zero"
        assert len(result["diagnostics"]) == 6
        for row in result["diagnostics"]:
            assert 0 < row["quasimode_residual_over_eps6"] < 6
            assert 0.8 < row["endpoint_ratio"] < 1.1
    elif name == "inverse_checks":
        assert result["symbolic"]["residual_coefficients_minus1_through3"] == "all exactly zero"
        for row in result["numeric"]["rows"]:
            assert abs(float(row["explicit_scaled_x_4_3_log"])) < fixture["inverse_max_scaled_explicit_error"]
            assert abs(float(row["newton2_scaled_x_5_3_log7"])) < fixture["inverse_max_scaled_newton2_error"]
    elif name == "forward_evidence":
        for row in result["numerics"]:
            value = fixture["forward_relative_three"].get(str(row["n"]))
            if value is not None:
                assert abs(row["relative_three_corrections"]-value) < fixture["floating_regression_absolute_tolerance"]
    else:
        raise AssertionError(f"Unrecognized advertised check {name}")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n",type=int,default=20000)
    parser.add_argument("--order",type=int,default=8)
    parser.add_argument("--output-dir",type=Path,default=ROOT/"output")
    args=parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        parser.error("Assertions must be enabled; do not use python -O")
    if args.order < 4 or args.max_n < 1:
        parser.error("Require --order >= 4 and --max-n >= 1")
    output=args.output_dir.resolve()
    if output == ROOT or (ROOT in output.parents and output.relative_to(ROOT).parts[0] != "output"):
        parser.error("An in-package output directory must be beneath output/")
    output.mkdir(parents=True,exist_ok=True)
    manifest=ROOT/"SHA256SUMS"
    report={"status":"running","python":sys.version,"platform":platform.platform(),
            "parameters":{"max_n":args.max_n,"order":args.order},"tests":[],
            "limitations":"Formal/exact finite tests and floating-point diagnostics do not certify the analytic theorem, gamma, or forward remainder bounds"}
    result_path=output/"replay_results.json"
    started=time.monotonic()
    try:
        report["initial_manifest_verification"]=verify_manifest(manifest)
        report["dependency_versions"]={p:importlib.metadata.version(p) for p in ("numpy","scipy","sympy","mpmath")}
        fixture=json.loads((ROOT/"fixtures"/"expected.json").read_text())
        tasks=[("exact_recurrence",[]),("frozen_quasimode",[]),
               ("coefficients",["--order",str(args.order)]),("inverse_checks",[]),
               ("forward_evidence",["--max-n",str(args.max_n)])]
        environment=os.environ.copy()
        environment["PYTHONDONTWRITEBYTECODE"]="1"
        environment.pop("PYTHONOPTIMIZE",None)
        for name, extra in tasks:
            verification=verify_manifest(manifest)
            json_path=output/f"{name}.json"
            command=[sys.executable,str(ROOT/f"{name}.py"),*extra,"--output",str(json_path)]
            print(f"Running {name} (manifest verified)",flush=True)
            test_started=time.monotonic()
            with (output/f"{name}.stdout.log").open("w") as stdout, (output/f"{name}.stderr.log").open("w") as stderr:
                completed=subprocess.run(command,cwd=ROOT,env=environment,stdout=stdout,stderr=stderr,check=False)
            test={"name":name,"returncode":completed.returncode,
                  "seconds":round(time.monotonic()-test_started,6),
                  "manifest_verification":verification,"command":command}
            report["tests"].append(test)
            if completed.returncode:
                raise RuntimeError(f"{name} failed; inspect {name}.stderr.log")
            result=json.loads(json_path.read_text())
            check_fixture(name,result,fixture)
            test["fixture_check"]="passed"
            test["output_sha256"]=digest(json_path)
            result_path.write_text(json.dumps(report,indent=2)+"\n")
        report["final_manifest_verification"]=verify_manifest(manifest)
        report["status"]="passed"
    except Exception as error:
        report["status"]="failed"
        report["error"]=f"{type(error).__name__}: {error}"
        print(report["error"],file=sys.stderr)
    report["total_seconds"]=round(time.monotonic()-started,6)
    result_path.write_text(json.dumps(report,indent=2)+"\n")
    print(f"Replay {report['status']}: {result_path}",flush=True)
    return 0 if report["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
