"""Reproduce whole-module source metrics without executing historical code."""
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


def metrics(path):
    raw = path.read_bytes()
    tree = ast.parse(raw)
    for node in ast.walk(tree):
        if isinstance(node, (ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if node.body and isinstance(node.body[0], ast.Expr):
                value = node.body[0].value
                if isinstance(value, ast.Constant) and isinstance(value.value, str):
                    node.body.pop(0)
                    if not node.body and not isinstance(node, ast.Module):
                        node.body.append(ast.Pass())
    normalized = (ast.unparse(tree) + "\n").encode()
    ignored = {
        tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT,
    }
    tokens = sum(t.type not in ignored for t in tokenize.tokenize(io.BytesIO(normalized).readline))
    return {
        "path": str(path.relative_to(ROOT)),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "raw_bytes": len(raw),
        "normalized_bytes": len(normalized),
        "tokens": tokens,
        "ast_nodes": sum(1 for _ in ast.walk(ast.parse(normalized))),
        "gzip9_raw_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
    }


def main():
    manifest = json.loads((ROOT / "evidence/corpus_manifest.json").read_text())
    census = []
    for path in sorted((ROOT / "source_corpus").glob("*.py")):
        row = metrics(path)
        if row["sha256"] != path.stem or path.stem not in manifest["python"]:
            raise ValueError("A frozen source hash does not match its identity")
        row["origins"] = manifest["python"][path.stem]["origins"]
        census.append(row)
    selected = [metrics(p) for p in sorted((ROOT / "code").glob("*.py"))]
    selected += [metrics(p) for p in sorted((ROOT / "reference").glob("*.py"))]
    selected += [metrics(p) for p in sorted((ROOT / "validation/composition").glob("ablation_*.py"))]
    output = {
        "python": platform.python_version(), "zlib": zlib.ZLIB_VERSION,
        "commit": manifest["commit"], "census_count": len(census),
        "selected": selected, "census": census,
    }
    (ROOT / "evidence/measurements.json").write_text(json.dumps(output, indent=2) + "\n")
    for row in selected:
        path = ROOT / row["path"]
        if row["path"].startswith("code/"):
            path.with_suffix(".py.gz").write_bytes(gzip.compress(path.read_bytes(), compresslevel=9, mtime=0))
        print(row["path"], row["normalized_bytes"], row["tokens"], row["ast_nodes"], row["gzip9_raw_bytes"])
    print("Frozen historical sources parsed, not executed:", len(census))


if __name__ == "__main__":
    main()
