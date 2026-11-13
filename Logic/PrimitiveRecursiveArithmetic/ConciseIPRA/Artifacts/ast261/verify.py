"""Reproduce the initialization refinement, metrics, and matched process checks.

No measured checker imports this helper. Run with CPython 3.12.14 for the
recorded normalization convention. Universal equivalence is proved in
report.tex, Section 4; the finite tests are supporting evidence only.
"""
import ast
import copy
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
        tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
PROGRAMS = ("controls/checker_ast262.py", "code/checker.py")


def measure(name):
    data = (ROOT / name).read_bytes()
    normalized = (ast.unparse(ast.parse(data)) + "\n").encode()
    return {
        "file": name,
        "significant_tokens": sum(t.type not in SKIP for t in
            tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "normalized_utf8_bytes": len(normalized),
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def structural_check():
    old = ast.parse((ROOT / PROGRAMS[0]).read_text())
    new = ast.parse((ROOT / PROGRAMS[1]).read_text())
    initial = old.body.pop(1)
    assert isinstance(initial, ast.Assign)
    assert len(initial.targets) == 1 and initial.targets[0].id == "k"
    assert ast.literal_eval(initial.value) == 0
    opener = old.body[1]
    assert isinstance(opener, ast.FunctionDef) and opener.name == "i"
    assert ast.literal_eval(opener.args.defaults[-1]) == 0
    opener.args.defaults[-1] = ast.NamedExpr(
        target=ast.Name(id="k", ctx=ast.Store()), value=ast.Constant(value=0))
    assert ast.dump(old, include_attributes=False) == ast.dump(new, include_attributes=False)
    # The bodies of i and c, the entry call, and ACCEPT output are identical.
    return {"only_change": "move k=0 into i's depth default",
            "all_function_bodies_identical": True,
            "packet_protocol_and_entry_call_identical": True}


def execute(name, data, optimized):
    command = [sys.executable, "-I", "-S", "-B"]
    if optimized:
        command.append("-O")
    command.append(str(ROOT / name))
    try:
        run = subprocess.run(command, input=data, capture_output=True, timeout=25)
    except subprocess.TimeoutExpired:
        return {"accepted": False, "exit_code": None, "exception": "TIMEOUT"}
    return {
        "accepted": run.returncode == 0 and run.stdout == b"ACCEPT\n",
        "exit_code": run.returncode,
        "exception": run.stderr.decode(errors="replace").splitlines()[-1]
                     if run.stderr else "",
    }


def main():
    structural = structural_check()
    rows = []
    paths = sorted((ROOT / "fixtures").glob("*.jsonl"))
    for path in paths:
        expected = not (path.name.startswith(("reject_", "future_witness"))
                        or path.name == "direct_false_zero_initializer.jsonl")
        tests = [("supplied", path.read_bytes(), expected)]
        if expected:
            lines = path.read_bytes().splitlines()
            tests.append(("false_public_goal", b"[0,[0]]\n" + b"\n".join(lines[1:]) + b"\n", False))
        for kind, data, intended in tests:
            for optimized in (False, True):
                for name in PROGRAMS:
                    rows.append({"fixture": path.name, "kind": kind,
                                 "optimized": optimized, "program": name,
                                 "expected": intended, **execute(name, data, optimized)})
    failures = [r for r in rows if r["accepted"] != r["expected"] or r["exception"] == "TIMEOUT"]
    metrics = {"python": sys.version,
               "normalization": "ast.unparse(ast.parse(complete source)) plus one LF",
               "programs": [measure(name) for name in PROGRAMS]}
    validation = {"python": sys.version, "structural_audit": structural,
                  "distinct_fixture_files": len(paths), "process_executions": len(rows),
                  "failures": failures, "results": rows}
    (ROOT / "evidence" / "metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    (ROOT / "evidence" / "validation.json").write_text(json.dumps(validation, indent=2) + "\n")
    print(json.dumps({"programs": metrics["programs"], "fixture_files": len(paths),
                      "executions": len(rows), "failures": len(failures)}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
