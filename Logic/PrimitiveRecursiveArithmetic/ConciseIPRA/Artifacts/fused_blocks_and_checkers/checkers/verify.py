"""Measure complete modules and check focused inherited and adversarial fixtures.

The checker programs do not import this module. Tests are finite evidence;
their universal equivalence argument is supplied separately.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
EXPECTED = {
    "code/checker_tokens239.py": (239, 261, 549),
    "code/checker_ast256.py": (245, 256, 580),
    "controls/control_tokens240.py": (240, 266, 551),
    "controls/control_return_ast261.py": (242, 261, 563),
    "controls/control_ast259.py": (252, 259, 595),
    "controls/control_bytes462.py": (267, 298, 462),
}
PROGRAMS = list(EXPECTED)[:4] + ["code/checker_readable.py"]


def measure(relative):
    path = ROOT / relative
    source = path.read_bytes()
    normalized = (ast.unparse(ast.parse(source)) + "\n").encode()
    return {
        "path": relative,
        "tokens": sum(t.type not in SKIP for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "normalized_bytes": len(normalized),
        "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256": hashlib.sha256(source).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def execute(relative, data, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(ROOT / relative))
    process = subprocess.run(command, input=data, capture_output=True, timeout=15)
    return {
        "accepted": process.returncode == 0 and process.stdout == b"ACCEPT\n",
        "exit_code": process.returncode,
        "exception": process.stderr.decode(errors="replace").splitlines()[-1]
                     if process.stderr else "",
    }


def boundary(relative):
    data = (ROOT / "fixtures/future_witness_before_major.jsonl").read_text()
    lines = iter(data.splitlines())
    reads = []

    def supplied_input():
        line = next(lines)
        reads.append(line)
        return line

    try:
        path = ROOT / relative
        exec(compile(path.read_text(), str(path), "exec"),
             {"input": supplied_input, "print": lambda *args: None})
        exception = "NONE"
    except Exception as exc:
        exception = type(exc).__name__
    return {"program": relative, "exception": exception,
            "lines_consumed": len(reads),
            "rejected_before_neutral_major": exception == "TypeError" and len(reads) == 2}


def main():
    metrics = [measure(path) for path in EXPECTED]
    failures = []
    for row in metrics:
        actual = tuple(row[k] for k in ("tokens", "ast_nodes", "normalized_bytes"))
        if actual != EXPECTED[row["path"]]:
            failures.append({"measurement": row["path"], "actual": actual,
                             "expected": EXPECTED[row["path"]]})
    fixtures = json.loads((ROOT / "fixtures/manifest.json").read_text())
    results = []
    for fixture in fixtures:
        data = (ROOT / fixture["path"]).read_bytes()
        for program in PROGRAMS:
            for optimized in (False, True):
                row = {**fixture, "program": program, "optimized": optimized,
                       **execute(program, data, optimized)}
                results.append(row)
                if row["accepted"] != row["expected"]:
                    failures.append(row)
    boundaries = [boundary(path) for path in PROGRAMS]
    failures.extend(row for row in boundaries if not row["rejected_before_neutral_major"])
    receipt = {"python": platform.python_version(), "metrics": metrics,
               "fixtures": len(fixtures), "isolated_process_executions": len(results),
               "scope_boundary_checks": boundaries, "failures": failures,
               "results": results,
               "status": "Finite regression evidence; the universal proof is separate."}
    (ROOT / "evidence/verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in (
        "python", "metrics", "fixtures", "isolated_process_executions",
        "scope_boundary_checks", "failures")}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
