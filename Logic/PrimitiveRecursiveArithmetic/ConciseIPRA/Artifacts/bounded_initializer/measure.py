"""Whole-module measurements; gzip is informational."""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zlib

ROOT = Path(__file__).resolve().parent

class StripDocstrings(ast.NodeTransformer):
    def visit_Module(self, node):
        return self.strip(node)
    def visit_FunctionDef(self, node):
        return self.strip(node)
    def visit_AsyncFunctionDef(self, node):
        return self.strip(node)
    def visit_ClassDef(self, node):
        return self.strip(node)
    def strip(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            v = node.body[0].value
            if isinstance(v, ast.Constant) and isinstance(v.value, str):
                node.body.pop(0)
        return node

def metrics(raw):
    tree = StripDocstrings().visit(ast.parse(raw.decode("utf-8")))
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    skip = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
            tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}
    tokens = sum(t.type not in skip for t in tokenize.tokenize(io.BytesIO(normalized).readline))
    return dict(raw_bytes=len(raw), normalized_bytes=len(normalized),
                normalized_tokens=tokens, ast_nodes=sum(1 for _ in ast.walk(tree)),
                gzip9_raw_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
                gzip9_normalized_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
                sha256=hashlib.sha256(raw).hexdigest())

def run(write=False):
    paths = ["code/checker.py", "code/checker_compact.py", "code/checker_ast.py",
             "code/readable_checker.py", "reference/current_bytes.py",
             "reference/current_ast.py", "reference/uniform_predecessor.py",
             "reference/arity_calculus.py"]
    result = dict(python=platform.python_version(), implementation=platform.python_implementation(),
                  zlib=zlib.ZLIB_VERSION, zlib_runtime=zlib.ZLIB_RUNTIME_VERSION, rows={})
    for name in paths:
        raw = (ROOT / name).read_bytes()
        result["rows"][name] = metrics(raw)
        if write and name.startswith("code/"):
            (ROOT / (name+".gz")).write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
    if write:
        (ROOT / "evidence/measurements.json").write_text(json.dumps(result, indent=2)+"\n")
    return result

if __name__ == "__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--write",action="store_true")
    args=parser.parse_args()
    print(json.dumps(run(args.write),indent=2))
