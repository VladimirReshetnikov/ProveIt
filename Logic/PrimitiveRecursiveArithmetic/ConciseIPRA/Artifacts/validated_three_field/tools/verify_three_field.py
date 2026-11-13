"""Reproduce canonical compilation and adversarial tests of the new protocol.

Run from the archive root: python3 tools/verify_three_field.py
Only the Python standard library is used. Receipts distinguish finite tests from
mathematical soundness. Both ordinary execution and python -O are exercised.
"""
from __future__ import annotations
import argparse
import concurrent.futures
import copy
import hashlib
import json
import subprocess
import sys
from pathlib import Path
from compile_three_field import compile_certificate


def malformed_record_translation(cert):
    """An explicit perturbation generator, not a correctness-preserving compiler."""
    if not isinstance(cert, list) or not cert:
        return cert
    records = []
    for record in cert[:-1]:
        if isinstance(record, list) and len(record) == 4:
            m, s, u, t = record
            inferred = [s, u] if s else [t] * 3
            records.append([s, u, t] if not m or m == inferred else [m, 0, 0])
        else:
            records.append(record)
    return records + [cert[-1]]


def run_case(job):
    root, case, checker, optimized = job
    try:
        result = subprocess.run(
            [sys.executable, *(["-O"] if optimized else []), str(root / checker)],
            input=json.dumps(case["certificate"]), text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=15)
        accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
        error = None if accepted else (
            result.stderr.splitlines()[-1] if result.stderr else f"exit {result.returncode}")
    except subprocess.TimeoutExpired:
        accepted, error = False, "timeout (not acceptance)"
    return {"case": case["name"], "checker": checker, "optimized": optimized,
            "expected": case["expected"], "accepted": accepted, "error": error}


def make_cases(root):
    originals = json.loads((root / "fixtures/supply_cases.json").read_text())["cases"]
    control = root / "controls/checker_strict_tokens317.py"
    cases = []
    for original in originals:
        if original["expected"]:
            cases.append({"name": "compiled_" + original["name"], "expected": True,
                          "certificate": compile_certificate(original["certificate"], control)})
    if not cases:
        raise ValueError("No canonical positive fixtures were supplied")
    seed = copy.deepcopy(cases[0]["certificate"])
    for name, goal in [
        ("false_zero_one", [1, [1]]), ("false_one_zero", [[1], 1]),
        ("public_old_zero", [0, 0]), ("public_even_alias", [2, 2]),
        ("public_free_slot", [99, 99]), ("public_negative_name", [-1, -1]),
        ("public_Q", [[1, 1]] * 3), ("public_empty_formula", []),
        ("public_scalar", 1), ("public_empty_term", [[], []]),
        ("public_boolean", [True, 1]), ("public_float", [1.0, 1]),
        ("public_null", [None, 1]), ("public_string", ["1", 1]),
        ("public_object", [{"a": 1}, 1]),
    ]:
        cases.append({"name": name, "expected": False, "certificate": seed[:-1] + [goal]})
    for j, record in enumerate([0, [], [0], [0, 0], [0, 0, 0, 0], None, True]):
        cert = copy.deepcopy(seed)
        cert[-2] = record
        cases.append({"name": f"bad_root_record_{j}", "expected": False, "certificate": cert})
    cases.append({"name": "missing_root_record", "expected": False,
                  "certificate": [seed[-1]]})
    for j, prefix in enumerate([None, True, 1.5, "unused", {"unused": 0}]):
        cases.append({"name": f"invalid_unused_prefix_{j}", "expected": False,
                      "certificate": [prefix] + seed})
    attack_prefixes = ("191_", "193_", "195_", "202_", "204_")
    for original in originals:
        if original["name"].startswith(attack_prefixes):
            cases.append({"name": "raw_attack_" + original["name"], "expected": False,
                          "certificate": malformed_record_translation(original["certificate"])})
    for original in list(cases):
        if original["expected"]:
            cases.append({"name": original["name"] + "_false_goal", "expected": False,
                          "certificate": original["certificate"][:-1] + [[1, [1]]]})
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    cases = make_cases(root)
    checkers = ["code/checker_tokens306.py", "code/checker_joint.py"]
    readable = "code/readable_three_field_strict.py"
    if (root / readable).is_file():
        checkers.append(readable)
    jobs = [(root, case, checker, optimized) for case in cases
            for checker in checkers for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(run_case, jobs))
    failures = [r for r in results if r["accepted"] != r["expected"]]
    receipt = {
        "python": sys.version, "scope": "finite canonical and adversarial tests; not a proof",
        "cases": len(cases), "positive_cases": sum(c["expected"] for c in cases),
        "executions": len(results), "failures": failures,
        "source_sha256": {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in checkers},
        "results": results,
    }
    (root / "fixtures/three_field_cases.json").write_text(json.dumps({"cases": cases}, indent=2) + "\n")
    (root / "evidence/three_field_verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "results"}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
