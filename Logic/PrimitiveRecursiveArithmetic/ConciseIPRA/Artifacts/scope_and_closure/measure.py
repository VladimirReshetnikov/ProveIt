"""Whole-program sizes, using the repository's existing convention."""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def main():
    rows = []
    for directory in ("reference", "code"):
        for path in sorted((ROOT / directory).glob("checker_*.py")):
            raw = path.read_bytes()
            tree = ast.parse(raw)
            normalized = (ast.unparse(tree) + "\n").encode()
            rows.append({
                "path": str(path.relative_to(ROOT)),
                "tokens": sum(t.type not in IGNORED for t in tokenize.generate_tokens(
                    io.StringIO(normalized.decode()).readline)),
                "ast_nodes": sum(1 for _ in ast.walk(tree)),
                "normalized_bytes": len(normalized),
                "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                "sha256": hashlib.sha256(raw).hexdigest(),
            })
    print(json.dumps({"python": platform.python_version(), "zlib": zlib.ZLIB_RUNTIME_VERSION,
                      "programs": rows}, indent=2))


if __name__ == "__main__":
    main()
