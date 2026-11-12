"""Reproduce the four-field composition profiles, using only the stdlib.

The acceptance modules import none of this support code. Run with CPython
3.12.14 for the frozen ast.unparse size measurements. This script executes
both ordinary and optimized isolated Python processes on the bundled inputs.
"""

import ast
import concurrent.futures
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}
EXPECTED_METRICS = {
    "code/checker_bytes.py": (267, 299, 495),
    "code/checker_native.py": (342, 391, 666),
    "controls/checker_bytes_499.py": (265, 301, 499),
    "controls/checker_bytes_502.py": (269, 301, 502),
    "controls/checker_native_673.py": (344, 393, 673),
}
GROUPS = (
    (
        "byte/progress",
        ("controls/checker_bytes_502.py", "code/checker_bytes.py"),
    ),
    (
        "byte/context",
        ("controls/checker_bytes_499.py", "code/checker_bytes.py"),
    ),
    (
        "native/proofs",
        ("controls/checker_native_673.py", "code/checker_native.py"),
    ),
    (
        "native/boundary",
        ("controls/checker_native_673.py", "code/checker_native.py"),
    ),
)


def measure(relative_path):
    raw = (ROOT / relative_path).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + "\n").encode()
    return {
        "path": relative_path,
        "significant_tokens": sum(
            t.type not in SKIP for t in tokenize.generate_tokens(
                io.StringIO(normalized.decode()).readline
            )
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
        "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def task_list():
    tasks = []
    for group, programs in GROUPS:
        cases = json.loads((ROOT / "tests" / group / "cases.json").read_text())
        for case in cases:
            for program in programs:
                for optimized in (False, True):
                    tasks.append({
                        "group": group,
                        "fixture": "tests/" + group + "/" + case["file"],
                        "program": program,
                        "optimized": optimized,
                        "expected": case["expected"],
                    })
    return tasks


def execute(task):
    command = [sys.executable, "-I", "-S", "-B"]
    if task["optimized"]:
        command.append("-O")
    command.append(str(ROOT / task["program"]))
    raw = (ROOT / task["fixture"]).read_bytes()
    result = subprocess.run(command, input=raw, capture_output=True, timeout=30)
    actual = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    return {
        **task,
        "actual": actual,
        "passed": actual == task["expected"],
        "fixture_sha256": hashlib.sha256(raw).hexdigest(),
    }


def main():
    metrics = [measure(path) for path in EXPECTED_METRICS]
    mismatches = []
    for row in metrics:
        got = tuple(row[key] for key in (
            "significant_tokens", "ast_nodes", "normalized_bytes"
        ))
        wanted = EXPECTED_METRICS[row["path"]]
        if got != wanted:
            mismatches.append({"path": row["path"], "expected": wanted, "actual": got})
    tasks = task_list()
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, tasks))
    failures = [row for row in results if not row["passed"]]
    report = {
        "python": platform.python_version(),
        "metric_reference_python": "3.12.14",
        "metrics": metrics,
        "metric_mismatches": mismatches,
        "process_executions": len(results),
        "failures": failures,
        "results": results,
        "scope": "Finite process evidence supplements the written preservation proofs.",
    }
    evidence = ROOT / "evidence" / "compositions"
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    if failures or mismatches:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
