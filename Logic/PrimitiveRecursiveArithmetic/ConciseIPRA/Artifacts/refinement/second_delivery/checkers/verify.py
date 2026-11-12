"""Reproduce measurements and check the five local checker transformations.

This is untrusted support. None of the measured acceptance modules imports it.
The finite executions supplement the phase-invariant proof in PROOF.txt.
"""
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    "native_tokens": [321, 371, 618],
    "native_ast": [323, 369, 622],
    "native_bytes": [334, 380, 596],
    "strict_size": [330, 380, 638],
    "strict_bytes": [340, 385, 621],
}


def measure(path):
    source = path.read_bytes()
    normalized = (ast.unparse(ast.parse(source)) + "\n").encode()
    return {
        "path": str(path.relative_to(ROOT)),
        "tokens": sum(t.type not in SKIP for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized),
        "sha256": hashlib.sha256(source).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def structural_audit():
    output = []
    for row in json.loads((ROOT / "transforms.json").read_text()):
        name = row["name"]
        baseline = (ROOT / "controls" / (name + ".py")).read_text()
        candidate = (ROOT / "code" / (name + ".py")).read_text()
        expected = baseline
        for replacement in row["replacements"]:
            if expected.count(replacement["from"]) != 1:
                raise ValueError("The stated old expression is not unique: " + name)
            expected = expected.replace(replacement["from"], replacement["to"])
        exact = ast.dump(ast.parse(expected)) == ast.dump(ast.parse(candidate))
        hashes = (
            hashlib.sha256(baseline.encode()).hexdigest() == row["baseline_sha256"]
            and hashlib.sha256(candidate.encode()).hexdigest() == row["candidate_sha256"]
        )
        output.append({"name": name, "exact_ast_transform": exact,
                       "recorded_hashes_match": hashes})
    return output


def run(task):
    cmd = [sys.executable, "-I", "-S", "-B"]
    if task["optimized"]:
        cmd.append("-O")
    cmd.append(str(ROOT / task["program"]))
    payload = (ROOT / task["fixture"]).read_bytes()
    try:
        result = subprocess.run(cmd, input=payload, capture_output=True, timeout=30)
        accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
        return {**task, "accepted": accepted,
                "passed": accepted == task["expected"],
                "fixture_sha256": hashlib.sha256(payload).hexdigest()}
    except subprocess.TimeoutExpired:
        return {**task, "accepted": False, "passed": False, "timeout": True}


def main():
    metrics = []
    for name, wanted in EXPECTED.items():
        for folder in ("controls", "code"):
            row = measure(ROOT / folder / (name + ".py"))
            if folder == "code":
                row["expected_metric"] = wanted
                row["metric_matches"] = [row[k] for k in
                    ("tokens", "ast_nodes", "normalized_bytes")] == wanted
            metrics.append(row)
    audits = structural_audit()
    tasks = []
    for name in EXPECTED:
        groups = ("native",) if name.startswith("native") else (
            "strict_proofs", "strict_boundary")
        for group in groups:
            directory = ROOT / "fixtures" / group
            for case in json.loads((directory / "cases.json").read_text()):
                for folder in ("controls", "code"):
                    for optimized in (False, True):
                        tasks.append({
                            "name": name,
                            "program": folder + "/" + name + ".py",
                            "fixture": "fixtures/" + group + "/" + case["file"],
                            "optimized": optimized, "expected": case["expected"],
                        })
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        checks = list(pool.map(run, tasks))
    failures = [r for r in checks if not r["passed"]]
    pairs = {}
    for row in checks:
        key = (row["name"], row["fixture"], row["optimized"])
        pairs.setdefault(key, []).append(row["accepted"])
    differential_failures = [list(key) for key, values in pairs.items()
                             if len(values) != 2 or values[0] != values[1]]
    arithmetic = {
        "nonnegative_integer_examples": 10000,
        "parity_identity_holds": all(
            bool(not a or a > 1 == a % 2) == (a % 2 == (a > 1))
            for a in range(10000)),
        "negative_even_counterexample": {
            "a": -2, "old": bool(not -2 or -2 > 1 == -2 % 2),
            "new": (-2 % 2 == (-2 > 1))},
        "boolean_product_examples": 4,
        "boolean_product_holds": all(
            bool(delta and predicate) == bool(delta * predicate)
            for delta in (0, 1) for predicate in (False, True)),
        "scope": "Finite examples illustrate the elementary universal proof; they do not prove checker soundness.",
    }
    report = {
        "python": platform.python_version(), "reference_python": "3.12.14",
        "metrics": metrics, "structural_audits": audits,
        "process_executions": len(checks),
        "matched_execution_pairs": len(pairs),
        "failed_expectations": failures,
        "differential_failures": differential_failures,
        "arithmetic_examples": arithmetic, "checks": checks,
        "scope": "Only the public-coordinate predicate and the noncallable rejection sentinel change. Mathematical equivalence and completeness are inherited through exact acceptance equivalence, subject to each documented interface.",
    }
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "checks"}, indent=2))
    if failures or differential_failures or not all(
        r["exact_ast_transform"] and r["recorded_hashes_match"] for r in audits
    ) or not all(r.get("metric_matches", True) for r in metrics):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
