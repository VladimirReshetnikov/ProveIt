#!/usr/bin/env python3
"""Offline measurements and focused counterexample reproduction.

No candidate here is claimed to be a new qualifying proof checker.
The rejected experiment is deliberately expected to accept a false equation.
"""
import ast
import gzip
import hashlib
import io
import json
import platform
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED_TOKENS = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
    tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT,
}


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "tokens": sum(token.type not in IGNORED_TOKENS for token in tokens),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "raw_gzip9_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "normalized_gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def run_case(program, name, data, expected, optimized):
    command = [sys.executable]
    if optimized:
        command.append("-O")
    command.append(str(ROOT / program))
    try:
        result = subprocess.run(
            command, input=data, text=True, capture_output=True,
            timeout=10, cwd=ROOT, check=False,
        )
        accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
        last_error_line = result.stderr.strip().splitlines()[-1:]
        exception = last_error_line[0].split(":", 1)[0] if last_error_line else None
        return {
            "program": program, "case": name, "optimized": optimized,
            "expected_acceptance": expected, "accepted": accepted,
            "returncode": result.returncode, "exception_type": exception,
            "passed": accepted == expected,
        }
    except subprocess.TimeoutExpired:
        return {
            "program": program, "case": name, "optimized": optimized,
            "expected_acceptance": expected, "accepted": False,
            "timeout": True, "passed": False,
        }


def main():
    provenance = json.loads((ROOT / "controls/PROVENANCE.json").read_text())
    measurements = []
    for control in provenance["controls"]:
        actual = measure(ROOT / control["file"])
        expected = control["expected"]
        metrics_match = all(actual[key] == value for key, value in expected.items())
        hashes_match = all(
            actual[key] == control[key]
            for key in ("raw_sha256", "normalized_sha256")
        )
        measurements.append({
            "file": control["file"], "role": "inherited_control",
            **actual, "expected": expected, "metrics_match": metrics_match,
            "hashes_match": hashes_match,
        })
    for name in (
        "experiments/REJECTED_UNSOUND_packet_floor.py",
        "experiments/LOCAL_REPAIR_NOT_CERTIFIED.py",
    ):
        measurements.append({"file": name, "role": "experiment", **measure(ROOT / name)})

    attack = json.loads((ROOT / "fixtures/packet_floor_false_goal.json").read_text())
    cases = {"false_goal_attack": attack}
    for name in ("zero_computation", "successor_computation", "inferred_major"):
        cases[name] = json.loads((ROOT / f"fixtures/{name}.json").read_text())

    programs = (
        ("controls/compact_tokens239.py", "jsonl", False),
        ("experiments/REJECTED_UNSOUND_packet_floor.py", "array", True),
        ("experiments/LOCAL_REPAIR_NOT_CERTIFIED.py", "array", False),
    )
    executions = []
    for program, framing, attack_acceptance in programs:
        for name, values in cases.items():
            data = (
                "".join(json.dumps(value, separators=(",", ":")) + "\n" for value in values[::-1])
                if framing == "jsonl"
                else json.dumps(values, separators=(",", ":")) + "\n"
            )
            expected = attack_acceptance if name == "false_goal_attack" else True
            for optimized in (False, True):
                executions.append(run_case(program, name, data, expected, optimized))

    failures = [row for row in executions if not row["passed"]]
    mismatches = [
        row["file"] for row in measurements
        if row["role"] == "inherited_control"
        and not (row["metrics_match"] and row["hashes_match"])
    ]
    receipt = {
        "status": "No new qualifying checker is claimed. Experimental repair is not certified.",
        "repository_commit": provenance["commit"],
        "runtime": {
            "implementation": platform.python_implementation(),
            "python_version": platform.python_version(),
            "reference_python_version": "3.12.14",
            "reference_version_matches": platform.python_version() == "3.12.14",
            "zlib_compile_version": zlib.ZLIB_VERSION,
            "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
        },
        "measurement_protocol": {
            "normalization": "ast.unparse(ast.parse(whole raw source)) plus one LF; no docstrings removed",
            "tokens": "Python tokens excluding encoding, comments, layout, and end markers",
            "ast_nodes": "Every node from ast.walk, including operator/context nodes",
            "gzip": "gzip.compress(..., compresslevel=9, mtime=0); measured for raw and normalized bytes",
        },
        "measurements": measurements,
        "executions": executions,
        "summary": {
            "inherited_controls": len(provenance["controls"]),
            "measured_modules": len(measurements),
            "isolated_executions": len(executions),
            "unexpected_execution_results": len(failures),
            "control_metric_or_hash_mismatches": mismatches,
            "all_expected_results_matched": not failures and not mismatches,
        },
        "limits": [
            "Passing finite tests does not prove arbitrary-certificate soundness or completeness.",
            "The unsound experiment intentionally accepts a false public equation.",
            "The repair is tested only as a local response to that counterexample.",
            "Record coordinates belong to different files and input contracts.",
            "Source normalization and gzip output can depend on Python and zlib versions.",
        ],
    }
    destination = ROOT / "evidence/reproduction.json"
    destination.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt["summary"], indent=2))
    if platform.python_version() != "3.12.14":
        print("Exact historical source counts use CPython 3.12.14.")
    if failures or mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
