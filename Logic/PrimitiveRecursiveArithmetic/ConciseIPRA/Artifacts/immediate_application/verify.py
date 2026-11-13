"""Reproduce source sizes, structural audits, and matched checker tests.

Only the four measured acceptance modules read proof certificates.
This script and the AST auditor are untrusted validation support.
"""
import ast
import concurrent.futures
import hashlib
import importlib.util
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
    "controls/checker487.py": [276, 308, 487],
    "code/checker479.py": [272, 304, 479],
    "controls/checker646.py": [343, 392, 646],
    "code/checker637.py": [344, 392, 637],
    "controls/tokens248.py": [248, 277, 609],
    "controls/ast270.py": [254, 270, 608],
}
GROUPS = (
    ("byte/progress", "controls/checker487.py", "code/checker479.py"),
    ("byte/context", "controls/checker487.py", "code/checker479.py"),
    ("native/proofs", "controls/checker646.py", "code/checker637.py"),
    ("native/boundary", "controls/checker646.py", "code/checker637.py"),
)


def measure(name):
    raw = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + "\n").encode()
    compile(normalized, name, "exec")
    counts = [sum(t.type not in SKIP for t in tokenize.generate_tokens(
        io.StringIO(normalized.decode()).readline)),
        sum(1 for _ in ast.walk(ast.parse(normalized))), len(normalized)]
    return {"path": name, "tokens": counts[0], "ast_nodes": counts[1],
            "normalized_bytes": counts[2], "expected": EXPECTED[name],
            "metric_matches": counts == EXPECTED[name],
            "sha256": hashlib.sha256(raw).hexdigest(),
            "normalized_sha256": hashlib.sha256(normalized).hexdigest()}


def run(task):
    command = [sys.executable, "-I", "-S", "-B"]
    if task["optimized"]:
        command.append("-O")
    command.append(str(ROOT / task["program"]))
    payload = (ROOT / task["fixture"]).read_bytes()
    try:
        result = subprocess.run(command, input=payload,
                                capture_output=True, timeout=30)
        accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
        return {**task, "accepted": accepted,
                "passed": accepted == task["expected"],
                "fixture_sha256": hashlib.sha256(payload).hexdigest()}
    except subprocess.TimeoutExpired:
        return {**task, "accepted": False, "passed": False, "timeout": True}


def main():
    metrics = [measure(name) for name in EXPECTED]
    spec = importlib.util.spec_from_file_location(
        "syntax_auditor", ROOT / "tools/audit_equivalence.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    audits = [module.audit(style, ROOT / control, ROOT / candidate)
              for style, control, candidate in (
                  ("compact", "controls/checker487.py", "code/checker479.py"),
                  ("strict", "controls/checker646.py", "code/checker637.py"))]
    for audit in audits:
        for key in ("baseline", "candidate"):
            audit[key] = str(Path(audit[key]).relative_to(ROOT))
    tasks = []
    for group, control, candidate in GROUPS:
        cases = json.loads((ROOT / "tests" / group / "cases.json").read_text())
        for case in cases:
            for optimized in (False, True):
                for program in (control, candidate):
                    tasks.append({"group": group, "program": program,
                                  "optimized": optimized,
                                  "fixture": "tests/" + group + "/" + case["file"],
                                  "expected": case["expected"]})
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, tasks))
    failures = [r for r in results if not r["passed"]]
    report = {"python": platform.python_version(),
              "reference_python": "3.12.14", "metrics": metrics,
              "structural_audits": audits, "process_executions": len(results),
              "distinct_cases": len(results) // 4,
              "failed_expectations": failures,
              "scope": "Tests supplement the written universal equivalence proof.",
              "results": results}
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/verification.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    if failures or not all(m["metric_matches"] for m in metrics):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
