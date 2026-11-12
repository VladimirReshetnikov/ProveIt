#!/usr/bin/env python3
"""Reproduce the complete-source measurements and focused checker tests.

This script is untrusted test infrastructure. Every test runs a standalone
checker process; the acceptance checks do not use Python assertions.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    "reference/checker_compact_506.py",
    "code/checker_compact.py",
    "reference/checker_guarded_exact_control.py",
    "code/checker_guarded_exact.py",
]
EXPECTED_METRICS = [
    {"tokens": 267, "ast_nodes": 303, "normalized_bytes": 506},
    {"tokens": 269, "ast_nodes": 301, "normalized_bytes": 502},
    {"tokens": 461, "ast_nodes": 521, "normalized_bytes": 1176},
    {"tokens": 463, "ast_nodes": 519, "normalized_bytes": 1172},
]
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
    tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    source = path.read_bytes()
    normalized = ast.unparse(ast.parse(source)) + "\n"
    tree = ast.parse(normalized)
    return {
        "tokens": sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized.encode("utf-8")),
        "source_sha256": hashlib.sha256(source).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized.encode()).hexdigest(),
    }


def run(program, payload, optimized):
    command = [sys.executable] + (["-O"] if optimized else []) + [str(ROOT / program)]
    result = subprocess.run(command, input=payload, capture_output=True, timeout=20)
    return result.returncode == 0 and result.stdout == b"ACCEPT\n"


def main():
    failures = []
    metrics = {}
    for name, expected in zip(PROGRAMS, EXPECTED_METRICS):
        actual = measure(ROOT / name)
        metrics[name] = actual
        if any(actual[key] != value for key, value in expected.items()):
            failures.append({"metric": name, "expected": expected, "actual": actual})
    rows = []

    def check(name, payload, program, optimized, expected):
        accepted = run(program, payload, optimized)
        row = {"case": name, "program": program, "optimized": optimized,
               "expected": expected, "accepted": accepted}
        rows.append(row)
        if accepted != expected:
            failures.append(row)

    for case in json.loads((ROOT / "fixtures/cases.json").read_text()):
        data = (ROOT / "fixtures" / case["file"]).read_bytes()
        for optimized in (False, True):
            for number, program in enumerate(PROGRAMS):
                expected = case["expected"] and (number < 2 or case["public_goal"])
                check(case["name"], data, program, optimized, expected)

    # The arity suite distinguishes the changed raw alias behavior from
    # the unchanged canonical theorem language.
    arities = json.loads((ROOT / "fixtures/arity/expected.json").read_text())
    for name, expected in arities.items():
        data = (ROOT / "fixtures/arity" / (name + ".json")).read_bytes()
        for optimized in (False, True):
            for number in (0, 1):
                check("arity/" + name, data, PROGRAMS[number], optimized, expected[number])

    # This witness confirms that eager evaluation can reject an old raw
    # trace without changing the theorem set on canonical public goals.
    data = (ROOT / "fixtures/eager_control_only.json").read_bytes()
    for optimized in (False, True):
        for number, program in enumerate(PROGRAMS):
            check("eager_control_only", data, program, optimized, number % 2 == 0)

    # Exact alphabet validation covers unused certificate prefixes as well.
    valid = json.loads((ROOT / "fixtures/computation_zero_local.json").read_text())
    malformed = [True, False, None, 0.0, 1.5, "annotation", {"x": 0}]
    for number, value in enumerate(malformed):
        data = json.dumps([value] + valid).encode()
        for optimized in (False, True):
            for program in PROGRAMS[2:]:
                check("invalid_unused_prefix_" + str(number), data, program, optimized, False)
    for number, payload in enumerate([[], [[0, [0]]], [0], [[]], [[True, True]]]):
        for optimized in (False, True):
            for program in PROGRAMS[2:]:
                check("invalid_public_goal_" + str(number), json.dumps(payload).encode(),
                      program, optimized, False)
    report = {
        "python": platform.python_version(),
        "metric_baseline": "CPython 3.12.14; ast.unparse plus one LF",
        "metrics": metrics,
        "process_executions": len(rows),
        "expected_acceptances": sum(row["expected"] for row in rows),
        "expected_rejections": sum(not row["expected"] for row in rows),
        "failures": failures,
        "checks": rows,
        "limitations": "Finite implementation checks; universal claims use the written proofs.",
    }
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "checks"}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
