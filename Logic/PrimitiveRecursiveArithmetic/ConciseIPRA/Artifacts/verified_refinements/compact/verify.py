"""Reproduce the exact control-flow refactoring and matched CLI checks."""
from pathlib import Path
import ast
import hashlib
import io
import json
import subprocess
import sys
import tokenize

ROOT = Path(__file__).resolve().parent


def measure(path):
    source = path.read_text()
    tree = ast.parse(source)
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
               tokenize.NL, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT}
    return {"file": path.name,
            "tokens": sum(t.type not in ignored for t in
                          tokenize.generate_tokens(io.StringIO(normalized).readline)),
            "ast": sum(1 for _ in ast.walk(tree)),
            "bytes": len(normalized.encode()),
            "sha256": hashlib.sha256(source.encode()).hexdigest()}


control = ast.parse((ROOT / "control495.py").read_text())
function = control.body[1]
opener, test, packet, continuation = function.body
assert isinstance(test, ast.If)
assert isinstance(test.test.ops[0], ast.In)
assert len(test.body) == 1 and isinstance(test.body[0], ast.Return)
assert test.body[0].value is None and not test.orelse
test.test.ops = [ast.NotIn()]
test.body = [packet, continuation]
function.body = [opener, test]
assert ast.dump(control) == ast.dump(ast.parse((ROOT / "checker.py").read_text()))

cases = json.loads((ROOT / "fixtures/cases.json").read_text())
checks = []
for case in cases:
    payload = (ROOT / "fixtures" / case["file"]).read_bytes()
    for optimized in (False, True):
        outcomes = []
        for name in ("control495.py", "checker.py"):
            command = [sys.executable, "-I", "-S", "-B"]
            if optimized:
                command.append("-O")
            command.append(str(ROOT / name))
            result = subprocess.run(command, input=payload, capture_output=True,
                                    timeout=30)
            accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
            outcomes.append(accepted)
            checks.append({"case": case["file"], "checker": name,
                           "optimized": optimized, "accepted": accepted,
                           "expected": case["expected"],
                           "passed": accepted == case["expected"]})
        assert outcomes[0] == outcomes[1]

report = {"python": sys.version, "exact_ast_transform_verified": True,
          "metrics": [measure(ROOT / name) for name in
                      ("control495.py", "checker.py")],
          "checks": checks,
          "cli_checks": len(checks),
          "failures": sum(not c["passed"] for c in checks),
          "limits": ["Exact refactoring of the inherited compact checker.",
                     "Does not add public-goal grammar validation.",
                     "Does not delete an arithmetic or logical rule.",
                     "Improves bytes and one AST node against its matched control; not all global minima."]}
(ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: report[key] for key in
                 ("exact_ast_transform_verified", "metrics", "cli_checks", "failures")}, indent=2))
if report["failures"]:
    raise SystemExit(1)
