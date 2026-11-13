#!/usr/bin/env python3
"""Read-only source census. Never imports or executes the measured sources.

Usage:
    python3 measure_corpus.py /path/to/ProveIt > census.json
    python3 measure_corpus.py path/to/checker.py path/to/package.zip

Counts complete normalized modules, including parser and output. Leading
module/class/function docstrings are removed before ast.unparse, following
the unified article's normalization protocol. Empty class/function bodies
receive a Pass node so the normalized program remains syntactically valid.
The script does NOT classify a source as a sound, complete proof checker.
Small builders, utilities, packed wrappers and rejected experiments occur
in this corpus. Consult baseline_manifest.json for qualified comparisons.

Exact recorded measurements use CPython 3.12.14. Standard-library only.
"""
import argparse
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tokenize
import zipfile

IGNORED = {
    tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
    tokenize.DEDENT, tokenize.ENCODING, tokenize.ENDMARKER,
}
LIMIT = 64 * 1024 * 1024
MAX_ARCHIVE_DEPTH = 4


class RemoveDocstrings(ast.NodeTransformer):
    def generic_visit(self, node):
        node = super().generic_visit(node)
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            if (node.body and isinstance(node.body[0], ast.Expr)
                    and isinstance(node.body[0].value, ast.Constant)
                    and isinstance(node.body[0].value.value, str)):
                node.body.pop(0)
            if not node.body and not isinstance(node, ast.Module):
                node.body.append(ast.Pass())
        return node


def source_metrics(data):
    encoding, _ = tokenize.detect_encoding(io.BytesIO(data).readline)
    source = data.decode(encoding)
    tree = ast.fix_missing_locations(RemoveDocstrings().visit(ast.parse(source)))
    normalized = ast.unparse(tree) + "\n"
    encoded = normalized.encode("utf-8")
    return {
        "tokens": sum(t.type not in IGNORED for t in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(encoded),
        "raw_bytes": len(data),
        "raw_sha256": hashlib.sha256(data).hexdigest(),
        "normalized_sha256": hashlib.sha256(encoded).hexdigest(),
        "gzip9_normalized_bytes": len(gzip.compress(encoded, compresslevel=9, mtime=0)),
        "classification": "unclassified source; metrics do not establish checker eligibility",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="+", type=Path)
    args = parser.parse_args()
    records, errors, omissions = [], [], []

    def visit_bytes(label, data, depth=0):
        if len(data) > LIMIT:
            omissions.append({"path": label, "reason": "file exceeds 64 MiB limit"})
            return
        try:
            if label.endswith(".py"):
                records.append({"path": label, **source_metrics(data)})
            elif label.endswith(".py.gz"):
                with gzip.GzipFile(fileobj=io.BytesIO(data)) as stream:
                    decoded = stream.read(LIMIT + 1)
                if len(decoded) > LIMIT:
                    omissions.append({"path": label, "reason": "gzip payload exceeds 64 MiB limit"})
                else:
                    records.append({"path": label, **source_metrics(decoded)})
            elif label.endswith(".zip"):
                if depth >= MAX_ARCHIVE_DEPTH:
                    omissions.append({"path": label, "reason": "nested archive depth limit"})
                    return
                with zipfile.ZipFile(io.BytesIO(data)) as archive:
                    for entry in sorted(archive.infolist(), key=lambda e: e.filename):
                        if entry.is_dir() or not entry.filename.endswith((".py", ".py.gz", ".zip")):
                            continue
                        child = label + "!" + entry.filename
                        if entry.file_size > LIMIT:
                            omissions.append({"path": child, "reason": "archive entry exceeds 64 MiB limit"})
                        else:
                            visit_bytes(child, archive.read(entry), depth + 1)
        except Exception as exc:
            errors.append({"path": label, "type": type(exc).__name__, "error": str(exc)})

    for path in args.paths:
        # Accept either a whole ProveIt checkout or the ConciseIPRA subtree.
        project = path / "Logic/PrimitiveRecursiveArithmetic/ConciseIPRA"
        if project.is_dir():
            path = project
        if path.is_dir():
            if (path / "Artifacts").is_dir():
                roots = [path / "Artifacts", path / "docs/incoming"]
            else:
                roots = [path]
            for root in roots:
                if not root.exists():
                    continue
                for file in sorted(root.rglob("*")):
                    if file.is_file() and file.name.endswith((".py", ".py.gz", ".zip")):
                        visit_bytes(str(file), file.read_bytes())
        elif path.is_file():
            visit_bytes(str(path), path.read_bytes())
        else:
            errors.append({"path": str(path), "type": "MissingPath", "error": "input does not exist"})
    result = {
        "runtime": sys.version,
        "normalization": "Remove leading module/class/function docstrings recursively; insert Pass in any resulting empty class/function body; ast.unparse of the whole module plus one LF",
        "source_occurrences": len(records),
        "distinct_raw_sources": len({r["raw_sha256"] for r in records}),
        "distinct_normalized_sources": len({r["normalized_sha256"] for r in records}),
        "eligible_minima": None,
        "eligibility_warning": "This census measures sources, not soundness or completeness. It deliberately does not infer frontier minima.",
        "errors": errors,
        "omissions": omissions,
        "sources": records,
    }
    print(json.dumps(result, indent=2, ensure_ascii=True))
    return 1 if errors or omissions else 0


if __name__ == "__main__":
    raise SystemExit(main())
