"""Measure four complete modules and replay the targeted inherited fixtures.

This is untrusted reproduction support. None of the checkers imports it.
"""

from pathlib import Path
import ast
import concurrent.futures
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
PROGRAMS = {
    "tokens": ("controls/tokens251.py", "code/tokens250.py"),
    "bytes": ("controls/bytes499.py", "code/bytes498.py"),
}


def metrics(relative):
    raw = (ROOT / relative).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + "\n").encode()
    return {"path": relative,
            "significant_tokens": sum(t.type not in SKIP for t in
                                      tokenize.generate_tokens(
                                          io.StringIO(normalized.decode()).readline)),
            "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
            "normalized_bytes": len(normalized),
            "sha256": hashlib.sha256(raw).hexdigest()}


def execute(task):
    case, program, optimized = task
    payload = (ROOT / case["fixture"]).read_bytes()
    if hashlib.sha256(payload).hexdigest() != case["sha256"]:
        raise ValueError("fixture bytes differ from the frozen source")
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    result = subprocess.run(command + [str(ROOT / program)], input=payload,
                            capture_output=True, timeout=20)
    actual = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    return {"profile": case["profile"], "fixture": case["fixture"],
            "program": program, "optimized": optimized,
            "expected_acceptance": case["expected"], "accepted": actual,
            "exit_code": result.returncode}


def main():
    cases = json.loads((ROOT / "fixtures/cases.json").read_text())
    tasks = [(case, program, optimized)
             for case in cases
             for program in PROGRAMS[case["profile"]]
             for optimized in (False, True)]
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(execute, tasks))
    failures = [r for r in results if r["accepted"] != r["expected_acceptance"]]
    report = {"python": platform.python_version(),
              "scope": "40 global token-profile fixtures and 21 local byte-profile fixtures",
              "same_calculus_as_main_constantfree_presentation": False,
              "assurance": "finite implementation tests; not universal soundness proofs",
              "fixture_count": len(cases), "process_executions": len(results),
              "failures": failures,
              "metrics": [metrics(p) for pair in PROGRAMS.values() for p in pair],
              "results": results}
    (ROOT / "evidence/validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
