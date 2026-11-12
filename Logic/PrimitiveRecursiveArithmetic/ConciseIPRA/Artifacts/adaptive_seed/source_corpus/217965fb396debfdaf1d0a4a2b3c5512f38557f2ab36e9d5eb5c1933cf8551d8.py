"""Measure complete source files using the current drafts' normalization."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize


def measure(path):
    source = path.read_text()
    tree = ast.parse(source)
    for part in ast.walk(tree):
        body = getattr(part, "body", None)
        if (isinstance(body, list) and body and isinstance(body[0], ast.Expr)
                and isinstance(body[0].value, ast.Constant)
                and isinstance(body[0].value.value, str)):
            body.pop(0)
    normalized = ast.unparse(tree) + "\n"
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.INDENT,
               tokenize.DEDENT, tokenize.NEWLINE, tokenize.NL, tokenize.COMMENT}
    tokens = sum(t.type not in ignored
                 for t in tokenize.generate_tokens(io.StringIO(normalized).readline))
    return {"tokens": tokens, "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(normalized.encode()), "raw_bytes": len(source.encode()),
            "sha256": hashlib.sha256(source.encode()).hexdigest()}


def run():
    root = Path(__file__).resolve().parents[1]
    names = ["reference/frontier_tokens.py", "reference/frontier_structure.py",
             "reference/frontier_bytes.py", "code/native/baseline_checker.py",
             "code/native/checker.py"]
    result = {"python": platform.python_version(),
              "definition": "Remove docstrings; ast.unparse plus final newline; count significant tokens, AST nodes and UTF-8 bytes.",
              "programs": [{"path": name, **measure(root / name)} for name in names]}
    (root / "evidence" / "complete_checker_metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    return result


if __name__ == "__main__":
    run()
