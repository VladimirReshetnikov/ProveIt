"""Remeasure Python sources recursively inside a supplied directory of ZIPs.

Usage: python3 tools/audit_corpus.py /path/to/ProveIt/docs/drafts output.json
This inventories sources; classifying a source as a complete checker still
requires inspection. The supplied boundary classification records that review.
"""
import argparse
import ast
import gzip
import hashlib
import io
import json
import tokenize
import zipfile
from pathlib import Path

SKIP = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
        tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}


class Strip(ast.NodeTransformer):
    def clean(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body = node.body[1:]
        return node
    visit_Module = clean
    visit_FunctionDef = clean
    visit_AsyncFunctionDef = clean
    visit_ClassDef = clean


def census(directory):
    sources, archives = {}, set()
    def source(raw, origin):
        sha = hashlib.sha256(raw).hexdigest()
        if sha not in sources:
            tree = ast.fix_missing_locations(Strip().visit(ast.parse(raw)))
            normalized = (ast.unparse(tree) + "\n").encode()
            sources[sha] = {
                "sha": sha, "paths": [], "raw_bytes": len(raw),
                "bytes": len(normalized),
                "tokens": sum(t.type not in SKIP for t in
                              tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                "ast": sum(1 for _ in ast.walk(tree)),
                "gzip9": len(gzip.compress(raw, compresslevel=9, mtime=0)),
            }
        sources[sha]["paths"].append(origin)
    def archive(raw, origin):
        sha = hashlib.sha256(raw).hexdigest()
        if sha in archives:
            return
        archives.add(sha)
        with zipfile.ZipFile(io.BytesIO(raw)) as opened:
            for member in opened.infolist():
                if member.filename.endswith(".py"):
                    source(opened.read(member), origin + "!" + member.filename)
                elif member.filename.endswith(".zip"):
                    archive(opened.read(member), origin + "!" + member.filename)
    direct = sorted(directory.glob("*.zip"))
    for path in direct:
        archive(path.read_bytes(), path.name)
    return {"direct_archives": len(direct), "distinct_archives": len(archives),
            "distinct_sources": len(sources), "sources": list(sources.values())}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("output", type=Path)
    options = parser.parse_args()
    result = census(options.directory)
    options.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "sources"}, indent=2))
