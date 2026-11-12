"""Reproduce the strict632 versus strict637 regression suite.

Run with CPython 3.12: python3 verify_checker.py
Only the Python standard library is required. Both standalone checkers are
executed in isolated, no-site subprocesses, ordinarily and with -O. Test
results support the separate written all-input equivalence argument; they
are not a machine-checked proof of arithmetic soundness.
"""
from concurrent.futures import ThreadPoolExecutor
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
PROGRAMS = ("strict637", "strict632")
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def source_audit(name):
    path = ROOT / "checkers" / (name + ".py")
    raw = path.read_bytes()
    tree = ast.parse(raw)
    normalized = ast.unparse(tree) + "\n"
    return {
        "program": name,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_bytes": len(normalized.encode()),
        "significant_tokens": sum(
            token.type not in SKIP
            for token in tokenize.generate_tokens(io.StringIO(normalized).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "assert_nodes": sum(isinstance(node, ast.Assert) for node in ast.walk(tree)),
        "debug_name_references": sum(
            isinstance(node, ast.Name) and node.id == "__debug__"
            for node in ast.walk(tree)
        ),
    }


def run_case(task):
    case, program, optimized = task
    payload = (ROOT / case["fixture"]).read_bytes()
    if hashlib.sha256(payload).hexdigest() != case["sha256"]:
        raise ValueError("Fixture hash mismatch: " + case["fixture"])
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(ROOT / "checkers" / (program + ".py")))
    try:
        result = subprocess.run(command, input=payload, capture_output=True, timeout=20)
        accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
        stderr_lines = result.stderr.decode("utf-8", errors="replace").splitlines()
        return {
            "fixture": case["fixture"],
            "program": program,
            "optimized": optimized,
            "expected": case["expected"],
            "accepted": accepted,
            "exit_code": result.returncode,
            "stdout": result.stdout.decode("utf-8", errors="replace"),
            "diagnostic": stderr_lines[-1] if stderr_lines else "",
            "timeout": False,
        }
    except subprocess.TimeoutExpired:
        return {
            "fixture": case["fixture"], "program": program,
            "optimized": optimized, "expected": case["expected"],
            "accepted": False, "exit_code": None,
            "stdout": "", "diagnostic": "Timeout after 20 seconds", "timeout": True,
        }


def main():
    cases = json.loads((ROOT / "cases.json").read_text())
    audits = [source_audit(name) for name in PROGRAMS]
    old = (ROOT / "checkers/strict637.py").read_text()
    new = (ROOT / "checkers/strict632.py").read_text()
    before = "q = not str(p).strip('0123456789-[], ') and p.pop"
    after = "q = str(p).strip('0123456789-[], ') or p.pop"
    sole_change = old.count(before) == 1 and old.replace(before, after) == new
    jobs = [(case, program, optimized) for case in cases
            for program in PROGRAMS for optimized in (False, True)]
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run_case, jobs))
    failures = [r for r in results if r["timeout"] or r["accepted"] != r["expected"]]
    acceptance = {}
    for result in results:
        acceptance.setdefault(result["fixture"], []).append(result["accepted"])
    disagreement = [name for name, values in acceptance.items() if len(set(values)) != 1]
    assertion_free = all(not row["assert_nodes"] and not row["debug_name_references"]
                         for row in audits)
    report = {
        "status": "PASS" if not failures and not disagreement and sole_change and assertion_free else "FAIL",
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "acceptance_contract": "exit code 0 and stdout exactly ACCEPT followed by newline",
        "input_contract": "strict whole-input integer/list alphabet and canonical native public goal",
        "process_flags": ["-I", "-S", "-B"],
        "optimization_modes": ["ordinary", "-O"],
        "fixture_count": len(cases),
        "inherited_fixture_count": sum(c["origin"].startswith("incoming") for c in cases),
        "new_fixture_count": sum(c["origin"] == "new targeted regression" for c in cases),
        "expected_accepted_fixtures": sum(c["expected"] for c in cases),
        "expected_rejected_fixtures": sum(not c["expected"] for c in cases),
        "process_executions": len(results),
        "failures": failures,
        "cross_program_or_optimization_disagreements": disagreement,
        "sole_source_change_is_lexical_gate": sole_change,
        "no_assert_or_debug_gate": assertion_free,
        "source_audits": audits,
        "assurance": "Finite regression evidence plus syntactic source audit; not a formal proof of iPRA soundness.",
        "results": results,
    }
    (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key != "results"}, indent=2))
    if report["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
