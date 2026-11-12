"""Measure whole Python modules; gzip is an informational coordinate only."""
import ast
import gzip
import hashlib
import io
import json
import sys
import tokenize
from pathlib import Path


def measure(path):
    raw = Path(path).read_bytes()
    normalized = (ast.unparse(ast.parse(raw.decode("utf-8"))) + "\n").encode()
    ignored = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
               tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    return {
        "tokens": sum(t.type not in ignored for t in tokenize.generate_tokens(
            io.StringIO(normalized.decode()).readline)),
        "ast_nodes": len(list(ast.walk(ast.parse(normalized)))),
        "normalized_bytes": len(normalized),
        "gzip9_normalized": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "raw_bytes": len(raw),
        "gzip9_raw": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def all_measurements(root):
    paths = [root / "code/c7_checker.py", root / "code/m7_control.py"]
    paths += sorted((root / "reference/baselines").rglob("*.py"))
    return {
        "python": sys.version,
        "normalization": "ast.unparse(ast.parse(source)) + newline",
        "gzip": "gzip.compress(UTF-8 bytes, compresslevel=9, mtime=0)",
        "rows": [{"path": str(p.relative_to(root)), **measure(p)} for p in paths],
    }


if __name__ == "__main__":
    root = Path(__file__).resolve().parent.parent
    print(json.dumps(all_measurements(root), indent=2))
