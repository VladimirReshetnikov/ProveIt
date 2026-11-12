"""Whole-module measurements, gzip-9 receipts, and exact change ablations."""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


def measure(source):
    raw = source.encode() if isinstance(source, str) else source
    tree = ast.parse(raw.decode())
    normalized = (ast.unparse(tree) + "\n").encode()
    return {
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "normalized_tokens": sum(tok.type not in IGNORED for tok in
                                 tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
        "ast_nodes": len(list(ast.walk(tree))),
        "gzip9_raw": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def ablations():
    # Each displayed source is a complete module, not an isolated fragment.
    original = (ROOT / "reference/checkers/checker_bytes.py").read_text()
    old = """    if m:
        c(m, g)
        a = m in ([s, u], not s and [t] * 3) and i(t, u) == a and i(t, s) or a"""
    prechecked = original.replace(old, """    a = m and m in ([s, u], not s and [t] * 3) and i(t, u) == a and i(t, s) or a""").replace(
        "h = m * 3 if m", "h = c(m, g) or m * 3 if m")
    separated = prechecked.replace(
        "m and m in ([s, u], not s and [t] * 3)",
        "m in ([s, u], s and 1j or [t] * 3)")
    missing = separated.replace("t=None", "t=0j")
    stages = [("inherited certified-zero byte checker", original),
              ("pre-major goal check and folded major supply", prechecked),
              ("non-real sentinel removes falsy-major guard", separated),
              ("short missing-image sentinel", missing)]
    return [{"stage": label, **measure(ast.unparse(ast.parse(source)) + "\n")}
            for label, source in stages]


def main():
    names = ("checker.py", "checker_bytes.py", "checker_structure.py")
    rows = []
    for name in names:
        source = (ROOT / "code" / name).read_bytes()
        if source != (ast.unparse(ast.parse(source.decode())) + "\n").encode():
            raise ValueError("Not normalized: " + name)
        (ROOT / "code" / (name + ".gz")).write_bytes(gzip.compress(source, compresslevel=9, mtime=0))
        rows.append({"file": name, **measure(source)})
    result = {"python": platform.python_version(), "implementation": platform.python_implementation(),
              "zlib": zlib.ZLIB_RUNTIME_VERSION, "gzip_compresslevel": 9, "gzip_mtime": 0,
              "programs": rows, "ablations": ablations()}
    (ROOT / "evidence/kernel_metrics.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
