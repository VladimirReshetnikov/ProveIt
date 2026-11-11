"""Reproduce complete-module metrics under the pinned corpus conventions."""
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PROGRAMS = [
    ("matched_old_rules", "code/strict_old.py"),
    ("direct_q_rules", "code/strict_q.py"),
    ("repository_byte_profile", "reference/checkers/neutral_scope_checker.py"),
    ("repository_token_profile", "reference/checkers/prevalidated_elimination_checker_structure.py"),
    ("repository_ast_profile", "reference/checkers/coverage_and_kernel_checker_ast.py"),
    ("counter_vector_tradeoff", "experiments/counter_vectors/counter_vector_checker.py"),
]


def measure(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    ignored = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
               tokenize.DEDENT, tokenize.ENDMARKER, tokenize.ENCODING}
    tokens = sum(token.type not in ignored for token in
                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline))
    result = {
        "raw_bytes": len(raw), "normalized_bytes": len(normalized),
        "significant_tokens": tokens,
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "gzip9_raw_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }
    return result, raw, normalized


def main():
    rows = []
    destination = ROOT / "evidence" / "gzip"
    destination.mkdir(exist_ok=True)
    for label, filename in PROGRAMS:
        row, raw, normalized = measure(ROOT / filename)
        row.update(label=label, file=filename)
        rows.append(row)
        (destination / f"{label}.raw.py.gz").write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
        (destination / f"{label}.normalized.py.gz").write_bytes(
            gzip.compress(normalized, compresslevel=9, mtime=0))
    result = {
        "python": platform.python_version(), "zlib": zlib.ZLIB_RUNTIME_VERSION,
        "normalization": "Remove actual docstrings; ast.unparse; one final newline.",
        "charged": "Entire standalone module, including syntax validation and JSON/verdict driver.",
        "excluded": "Common Python runtime and standard library, under inherited convention.",
        "gzip": "compresslevel=9, mtime=0, wrapper included; informational only.",
        "rows": rows,
    }
    (ROOT / "evidence" / "measurements.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
