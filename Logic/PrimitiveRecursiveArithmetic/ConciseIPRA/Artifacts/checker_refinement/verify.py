"""Measure complete modules and rerun the frozen matched-contract fixtures.

Run with CPython 3.12.14 to reproduce the reference size metric exactly.
All code is standard-library-only. Acceptance modules import no support file.
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
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
    tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}
EXPECTED = {
    "controls/checker_bytes495.py": (267, 299, 495),
    "code/checker_bytes.py": (271, 304, 488),
    "controls/checker_native666.py": (342, 391, 666),
    "code/checker_native.py": (343, 392, 646),
}
GROUPS = (
    ("byte/progress", "controls/checker_bytes495.py", "code/checker_bytes.py"),
    ("byte/context", "controls/checker_bytes495.py", "code/checker_bytes.py"),
    ("native/proofs", "controls/checker_native666.py", "code/checker_native.py"),
    ("native/boundary", "controls/checker_native666.py", "code/checker_native.py"),
)


def measure(name):
    raw = (ROOT / name).read_bytes()
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + "\n").encode()
    compile(normalized, name, "exec")
    counts = (
        sum(t.type not in SKIP for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        sum(1 for _ in ast.walk(ast.parse(normalized))),
        len(normalized),
    )
    return {
        "path": name,
        "tokens": counts[0], "ast_nodes": counts[1], "normalized_bytes": counts[2],
        "expected": list(EXPECTED[name]), "metric_matches": counts == EXPECTED[name],
        "sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def run(task):
    command = [sys.executable, "-I", "-S", "-B"]
    if task["optimized"]:
        command.append("-O")
    command.append(str(ROOT / task["program"]))
    payload = (ROOT / task["fixture"]).read_bytes()
    result = subprocess.run(command, input=payload, capture_output=True, timeout=30)
    actual = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    return {
        **task, "accepted": actual, "passed": actual == task["expected"],
        "fixture_sha256": hashlib.sha256(payload).hexdigest(),
    }


def main():
    metrics = [measure(name) for name in EXPECTED]
    tasks = []
    for group, control, candidate in GROUPS:
        cases = json.loads((ROOT / "tests" / group / "cases.json").read_text())
        for case in cases:
            for optimized in (False, True):
                for program in (control, candidate):
                    tasks.append({
                        "group": group, "program": program, "optimized": optimized,
                        "fixture": "tests/" + group + "/" + case["file"],
                        "expected": case["expected"],
                    })
    with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(run, tasks))
    failures = [r for r in results if not r["passed"]]
    report = {
        "python": platform.python_version(),
        "reference_python": "3.12.14",
        "metrics": metrics, "process_executions": len(results),
        "failures": failures, "results": results,
        "scope": "Finite evidence supplements the universal execution simulation proof.",
    }
    (ROOT / "evidence").mkdir(exist_ok=True)
    (ROOT / "evidence/verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "results"}, indent=2))
    if failures or not all(m["metric_matches"] for m in metrics):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
