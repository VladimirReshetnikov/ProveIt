"""Reproduce the whole-JSON AST comparison and 80 standalone CLI checks.

No checker imports this harness. Uses the Python standard library only.
Run: python3 verify.py
The reference measurement interpreter is CPython 3.12.14.
"""
from pathlib import Path
import ast
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
PROGRAMS = {
    "control": ROOT / "controls" / "checker_ast271.py",
    "candidate": ROOT / "checker_ast269.py",
}
EXPECTED = {"control": (255, 271, 606), "candidate": (255, 269, 605)}
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    data = path.read_bytes()
    normalized = ast.unparse(ast.parse(data)) + "\n"
    return {
        "path": path.relative_to(ROOT).as_posix(),
        "significant_tokens": sum(
            t.type not in SKIP
            for t in tokenize.generate_tokens(io.StringIO(normalized).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_bytes": len(normalized.encode("utf-8")),
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized.encode()).hexdigest(),
    }


def execute(program, payload, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(program))
    try:
        result = subprocess.run(
            command, input=payload, capture_output=True, timeout=25
        )
    except subprocess.TimeoutExpired:
        return {"accepted": False, "timed_out": True, "return_code": None}
    return {
        "accepted": result.returncode == 0 and result.stdout == b"ACCEPT\n",
        "timed_out": False,
        "return_code": result.returncode,
        "stdout": result.stdout.decode("utf-8", errors="replace"),
    }


def main():
    rows = []
    fixture_counts = {}
    for category, expected in (("positive", True), ("negative", False)):
        fixtures = sorted((ROOT / "fixtures" / category).glob("*.json"))
        fixture_counts[category] = len(fixtures)
        for fixture in fixtures:
            payload = fixture.read_bytes()
            for optimized in (False, True):
                for name, program in PROGRAMS.items():
                    result = execute(program, payload, optimized)
                    rows.append({
                        "fixture": fixture.relative_to(ROOT).as_posix(),
                        "program": name,
                        "optimized": optimized,
                        "expected": expected,
                        **result,
                        "passed": not result["timed_out"]
                                  and result["accepted"] == expected,
                    })
    metrics = {name: measure(path) for name, path in PROGRAMS.items()}
    metric_checks = {
        name: tuple(row[key] for key in
                    ("significant_tokens", "ast_nodes", "normalized_bytes"))
              == EXPECTED[name]
        for name, row in metrics.items()
    }
    result = {
        "python_implementation": platform.python_implementation(),
        "python_version": platform.python_version(),
        "reference_python": "CPython 3.12.14",
        "repository_commit": "12197d86f63e9ec73b2d91399c4de2a8cb0077ee",
        "fixture_counts": fixture_counts,
        "standalone_cli_checks": len(rows),
        "failed_cli_checks": sum(not row["passed"] for row in rows),
        "metrics": metrics,
        "expected_metrics_match": all(metric_checks.values()),
        "metric_checks": metric_checks,
        "checks": rows,
        "scope": [
            "The candidate and control are complete standalone acceptance modules.",
            "They share the whole-JSON framing and exact ACCEPT newline marker.",
            "The compact input contract assumes finite exact-integer/list data.",
            "The public theorem claim uses canonical closed guarded goals.",
            "Positive regressions include public goals and auxiliary native Q goals.",
            "Finite tests supplement the written simulation; they do not prove it.",
            "Only the AST coordinate improves the documented compact envelope.",
            "No new logical or arithmetic axiom is deleted.",
        ],
    }
    destination = ROOT / "evidence" / "validation.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "fixture_counts": fixture_counts,
        "standalone_cli_checks": len(rows),
        "failed_cli_checks": result["failed_cli_checks"],
        "metrics": metrics,
        "expected_metrics_match": result["expected_metrics_match"],
    }, indent=2))
    return bool(result["failed_cli_checks"] or not result["expected_metrics_match"])


if __name__ == "__main__":
    raise SystemExit(main())
