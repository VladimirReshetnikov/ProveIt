"""Reproduce compact equivalence and meaningful companion boundary checks.

Run from any directory with Python 3.12.14 (the measured environment):
    python3 verification/verify.py

No third-party package, network access, or imported proof checker is used.
The default run checks all three compact implementations against every
frozen expected verdict, in ordinary and optimized Python, then checks the
strict companion on explicit accepted and rejected public inputs.
"""

from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import ast
import hashlib
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = {
    "control": "controls/bytes487.py",
    "candidate": "code/checker479.py",
    "readable": "code/checker_readable.py",
    "strict": "code/checker_strict.py",
}


def serialize(data):
    return json.dumps(data, separators=(",", ":"), ensure_ascii=True).encode() + b"\n"


def execute(program, payload, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    try:
        result = subprocess.run(
            command + [str(ROOT / PROGRAMS[program])], input=payload,
            capture_output=True, timeout=25,
        )
        return {
            "accepted": result.returncode == 0 and result.stdout == b"ACCEPT\n",
            "returncode": result.returncode,
            "timeout": False,
        }
    except subprocess.TimeoutExpired:
        return {"accepted": False, "returncode": None, "timeout": True}


def check_task(task):
    label, program, payload, expected, optimized, group = task
    return {
        "fixture": label, "program": program, "optimized": optimized,
        "expected": expected, "group": group,
        **execute(program, payload, optimized),
    }


def exact_source_checks():
    original = ast.parse((ROOT / "controls/strict_guarded_original.py").read_text())
    strict = ast.parse((ROOT / "code/checker_strict.py").read_text())
    candidate = ast.parse((ROOT / "code/checker479.py").read_text())

    def definition(tree, name):
        return next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef) and node.name == name)

    unchanged = {
        name: ast.dump(definition(original, name)) == ast.dump(definition(strict, name))
        for name in ("integer_list_tree", "public_term", "public_formula")
    }

    def kernel(tree):
        return next(node for node in tree.body if isinstance(node, ast.Assign)
                    and isinstance(node.targets[0], ast.Name)
                    and node.targets[0].id == "c")

    unchanged["strict_uses_exact_candidate_kernel"] = (
        ast.dump(kernel(strict)) == ast.dump(kernel(candidate))
    )
    if not all(unchanged.values()):
        raise ValueError("Strict validator or candidate kernel differs unexpectedly")
    return unchanged


def strict_cases():
    folder = ROOT / "verification/fixtures/byte/context"

    def fixture(name):
        return json.loads((folder / name).read_bytes())

    minimal = fixture("computation_zero_local.json")
    cases = [
        ("zero_computation", minimal, True),
        ("empty_certificate", [], False),
        ("false_equation", [[0, [0]]], False),
        ("scalar_goal", [0], False),
        ("unbound_positive_goal", [[3, 3]], False),
        ("unbound_negative_goal", [[-1, -1]], False),
        ("unguarded_D_goal", [[[5, 5]]], False),
        ("public_Q_goal", [[[0, 0], [0, 0], [0, 0]]], False),
        ("unused_boolean", [True] + minimal, False),
        ("unused_float", [0.0] + minimal, False),
        ("unused_object", [{}] + minimal, False),
        ("unused_string", ["unused"] + minimal, False),
        ("unused_null", [None] + minimal, False),
    ]
    for name in (
        "computation_successor_local.json", "transport_reflexivity_local.json",
        "guarded_literal_equation_introduction_local.json",
        "guarded_lift_elimination_local.json",
    ):
        cases.append((name, fixture(name), True))
    for name in (
        "future_witness_capture.json", "context_leak_attack.json",
        "false_float_capture.json",
    ):
        cases.append((name, fixture(name), False))
    scope = json.loads((ROOT / "verification/fixtures/scope/future_scope_attack.json").read_bytes())
    cases.append(("future_scope_attack.json", scope, False))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--companions-only", action="store_true",
        help="Reuse the initial 65-fixture equivalence receipt; run new readable/strict checks and the scope counterexample.",
    )
    parser.add_argument("--workers", type=int, default=8)
    args = parser.parse_args()
    source_checks = exact_source_checks()
    manifest = json.loads((ROOT / "verification/fixture_manifest.json").read_text())
    tasks = []
    for item in manifest["files"]:
        path = ROOT / item["path"]
        payload = path.read_bytes()
        if hashlib.sha256(payload).hexdigest() != item["sha256"]:
            raise ValueError("Frozen fixture hash mismatch: " + item["path"])
        programs = ["control", "candidate", "readable"]
        if args.companions_only and item["group"] != "scope_counterexample":
            programs = ["readable"]
        for program in programs:
            for optimized in (False, True):
                tasks.append((item["path"], program, payload,
                              item["expected_compact_acceptance"], optimized, item["group"]))
    for label, data, expected in strict_cases():
        for optimized in (False, True):
            tasks.append((label, "strict", serialize(data), expected, optimized, "strict_boundary"))

    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        rows = list(pool.map(check_task, tasks))
    failures = [row for row in rows if row["timeout"] or row["accepted"] != row["expected"]]
    comparisons = {}
    for row in rows:
        if row["program"] in ("control", "candidate"):
            comparisons.setdefault((row["fixture"], row["optimized"]), {})[row["program"]] = row["accepted"]
    mismatches = [
        {"fixture": key[0], "optimized": key[1], **verdicts}
        for key, verdicts in comparisons.items()
        if set(verdicts) == {"control", "candidate"}
        and verdicts["control"] != verdicts["candidate"]
    ]
    report = {
        "python": platform.python_version(),
        "mode": "companions_only" if args.companions_only else "full_reproduction",
        "frozen_fixture_count": len(manifest["files"]),
        "strict_case_count": len(strict_cases()),
        "process_executions": len(rows),
        "source_identity_checks": source_checks,
        "program_sha256": {
            name: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
            for name, path in PROGRAMS.items()
        },
        "failures": failures,
        "control_candidate_mismatches": mismatches,
        "results": rows,
        "assurance": "Finite regressions supplement the exact operational preservation proof; they do not independently prove the iPRA interpretation theorem.",
    }
    output = ROOT / "evidence" / ("companion_validation.json" if args.companions_only else "verification.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "results"}, indent=2))
    if failures or mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
