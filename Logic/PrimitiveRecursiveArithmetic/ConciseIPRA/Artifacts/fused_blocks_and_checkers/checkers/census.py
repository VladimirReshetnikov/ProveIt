"""Static census of Python source, including gzip and recursively nested ZIPs.

This measures text only; it does not execute repository programs. A syntactic
print('ACCEPT') flag is a search aid, not a soundness or eligibility decision.
"""
from pathlib import Path
import argparse
import ast
import gzip
import hashlib
import io
import json
import platform
import tokenize
import zipfile

SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE,
        tokenize.NL, tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


class DropDocstrings(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if node.body and isinstance(node.body[0], ast.Expr):
            value = node.body[0].value
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                node.body.pop(0)
        if not node.body and not isinstance(node, ast.Module):
            node.body.append(ast.Pass())
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path, help="ConciseIPRA directory")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    rows, errors = [], []

    def measure(name, data):
        try:
            tree = ast.parse(data)
            normalized = (ast.unparse(DropDocstrings().visit(tree)) + "\n").encode()
            tree = ast.parse(normalized)
            has_accept = any(
                isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
                and n.func.id == "print"
                and any(isinstance(a, ast.Constant) and a.value == "ACCEPT"
                        for a in n.args)
                for n in ast.walk(tree))
            rows.append({
                "path": name,
                "tokens": sum(t.type not in SKIP for t in tokenize.generate_tokens(
                    io.StringIO(normalized.decode()).readline)),
                "ast_nodes": len(list(ast.walk(tree))),
                "normalized_bytes": len(normalized),
                "sha256": hashlib.sha256(data).hexdigest(),
                "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
                "syntactic_accept_marker": has_accept,
            })
        except (SyntaxError, UnicodeError, ValueError) as exc:
            errors.append({"path": name, "error": type(exc).__name__})

    def visit(name, data):
        if name.endswith(".zip"):
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                for entry in archive.infolist():
                    if entry.filename.endswith((".py", ".gz", ".zip")):
                        visit(name + "!" + entry.filename, archive.read(entry))
        elif name.endswith(".gz"):
            try:
                measure(name + "!gunzip", gzip.decompress(data))
            except (OSError, EOFError) as exc:
                errors.append({"path": name, "error": type(exc).__name__})
        elif name.endswith(".py"):
            measure(name, data)

    for directory in (args.root / "Artifacts", args.root / "docs/incoming"):
        for path in sorted(directory.rglob("*")):
            if path.is_file() and path.suffix in (".py", ".gz", ".zip"):
                visit(str(path.relative_to(args.root)), path.read_bytes())
    result = {"python": platform.python_version(),
              "normalization": "Recursive leading docstring removal, Pass repair, ast.unparse + LF",
              "modules": len(rows),
              "unique_normalized_modules": len({r["normalized_sha256"] for r in rows}),
              "errors": errors, "rows": rows,
              "eligibility": "Manually reviewed separately; print-marker detection is not eligibility."}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in (
        "python", "modules", "unique_normalized_modules", "errors")}, indent=2))


if __name__ == "__main__":
    main()
