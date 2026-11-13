"""Measure complete modules under the pinned CPython normalization convention."""
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MODULES = [
    "compact/control_ast256.py",
    "compact/checker_ast255.py",
    "native/controls/checker_tokens317.py",
    "native/controls/checker_ast356.py",
    "native/controls/checker_bytes597.py",
    "native/code/checker_tokens315.py",
    "native/code/checker_ast353.py",
    "native/code/checker_bytes589.py",
    "native/code/readable_checker.py",
]
IGNORED = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
    tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
}


def measure(path):
    tree = ast.parse(path.read_text(encoding="utf-8"))
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        "significant_tokens": sum(t.type not in IGNORED for t in tokens),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized),
        "gzip9_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def main():
    result = {
        "python_version": platform.python_version(),
        "normalization": "ast.unparse(ast.parse(source)) followed by one LF",
        "modules": {name: measure(ROOT / name) for name in MODULES},
    }
    output = json.dumps(result, indent=2) + "\n"
    (ROOT / "evidence" / "measurements.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
