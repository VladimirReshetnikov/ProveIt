"""Reproduce the symbolic certificates, CLI checks, and full-module metrics."""
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


class WithoutDocstrings(ast.NodeTransformer):
    def visit_body(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node

    visit_Module = visit_body
    visit_FunctionDef = visit_body
    visit_AsyncFunctionDef = visit_body
    visit_ClassDef = visit_body


def metrics(path):
    raw = path.read_bytes()
    tree = ast.fix_missing_locations(WithoutDocstrings().visit(ast.parse(raw)))
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
               tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    count = sum(token.type not in ignored for token in
                tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {"normalized_tokens": count,
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(normalized.encode()),
            "raw_bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def main():
    generation = subprocess.run([sys.executable, str(ROOT / "producer.py")],
                                capture_output=True, text=True, check=True)
    rows = json.loads((ROOT / "cases.json").read_text())
    receipts = []
    for row in rows:
        certificate = ROOT / row["file"]
        for optimized in (False, True):
            command = [sys.executable] + (["-O"] if optimized else [])
            command.append(str(ROOT / "checker.py"))
            result = subprocess.run(command, input=certificate.read_text(),
                                    capture_output=True, text=True, timeout=30)
            accepted = result.returncode == 0 and result.stdout == "ACCEPT\n"
            correct_rejection = result.returncode != 0 and result.stdout == "REJECT\n"
            passed = accepted if row["expected"] else correct_rejection
            receipts.append({"name": row["name"], "optimized": optimized,
                             "expected": row["expected"], "passed": passed,
                             "exit": result.returncode, "stdout": result.stdout,
                             "stderr": result.stderr,
                             "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest()})
    summary = {"python": platform.python_version(), "implementation": platform.python_implementation(),
               "generation": json.loads(generation.stdout), "cli_runs": len(receipts),
               "all_passed": all(row["passed"] for row in receipts),
               "checker_metrics": metrics(ROOT / "checker.py"), "runs": receipts}
    (ROOT / "validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: value for k, value in summary.items() if k != "runs"}, indent=2))
    if not summary["all_passed"]:
        raise SystemExit("A verification case failed")


if __name__ == "__main__":
    main()
