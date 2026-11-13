"""Reproduce measurements of the experimental combined checker sources."""
import ast
import gzip
import hashlib
import io
import json
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HERE = ROOT / "code"
SKIP = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
    tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}

def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw.decode())
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
    normalized = (ast.unparse(tree) + "\n").encode()
    return {
        "path": str(path.relative_to(ROOT)),
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "significant_tokens": sum(
            token.type not in SKIP for token in
            tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
        ),
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "gzip9_raw_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }

paths = [
    ROOT / "reference" / ("source_dispatch_" + name)
    for name in ("checker.py", "checker_bytes.py", "checker_tokens.py")
]
paths += [
    HERE / name for name in (
        "checker.py", "checker_bytes.py",
        "checker_tokens.py", "strict_checker.py"
    )
]
paths += [
    ROOT / "reference/guarded_strict_checker.py",
    ROOT / "reference/old_scalar_strict_checker.py",
]
rows = [measure(path) for path in paths]
print(json.dumps(rows, indent=2))
