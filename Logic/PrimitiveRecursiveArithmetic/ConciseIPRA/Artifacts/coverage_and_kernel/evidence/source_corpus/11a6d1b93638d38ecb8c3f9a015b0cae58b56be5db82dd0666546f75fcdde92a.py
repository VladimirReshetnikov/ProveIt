"""Audit exact Python sources in current and nested proposal ZIP archives.

Usage: python3 audit_corpus.py PATH_TO_DRAFT_ZIPS [OUTPUT_DIRECTORY]
No source from a proposal is executed. Duplicate ZIPs and source byte strings
are identified by SHA-256. The manual frontier classification is reproduced
from reviewed hashes in classification.json next to this script.
"""

import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import sys
import tokenize
import zipfile
import zlib

IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL,
           tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT,
           tokenize.ENDMARKER}
COORDINATES = ("normalized_tokens", "ast_nodes", "normalized_bytes")


class StripDocstrings(ast.NodeTransformer):
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


def measure(raw):
    """The complete module is counted, including imports and public driver."""
    source = raw.decode("utf-8")
    tree = StripDocstrings().visit(ast.parse(source))
    normalized = (ast.unparse(tree) + "\n").encode("utf-8")
    tokens = tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
    return {
        "normalized_tokens": sum(token.type not in IGNORED for token in tokens),
        "ast_nodes": sum(1 for _ in ast.walk(tree)),
        "normalized_bytes": len(normalized),
        "raw_bytes": len(raw),
        "gzip9_raw_bytes": len(gzip.compress(raw, compresslevel=9, mtime=0)),
        "gzip9_normalized_bytes": len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        "sha256": hashlib.sha256(raw).hexdigest(),
    }


def audit(directory):
    sources, archives, errors = {}, {}, []

    def visit(data, path):
        digest = hashlib.sha256(data).hexdigest()
        if digest in archives:
            archives[digest]["paths"].append(path)
            return
        archives[digest] = {"sha256": digest, "bytes": len(data), "paths": [path]}
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            for name in archive.namelist():
                member_path = path + "!" + name
                if name.endswith(".zip"):
                    visit(archive.read(name), member_path)
                elif name.endswith(".py"):
                    raw = archive.read(name)
                    source_hash = hashlib.sha256(raw).hexdigest()
                    if source_hash in sources:
                        sources[source_hash]["paths"].append(member_path)
                        continue
                    try:
                        sources[source_hash] = {**measure(raw), "paths": [member_path]}
                    except Exception as error:
                        errors.append({"path": member_path, "error": str(error)})

    roots = sorted(Path(directory).glob("*.zip"))
    for path in roots:
        visit(path.read_bytes(), path.name)
    return {
        "python": platform.python_version(),
        "implementation": platform.python_implementation(),
        "zlib_runtime": zlib.ZLIB_RUNTIME_VERSION,
        "root_archive_count": len(roots),
        "unique_archive_count": len(archives),
        "unique_source_count": len(sources),
        "archives": list(archives.values()),
        "sources": list(sources.values()),
        "errors": errors,
    }


def classify(result):
    classification = json.loads(Path(__file__).with_name("classification.json").read_text())
    rows = {row["sha256"]: row for row in result["sources"]}
    frontier = [rows[digest] for digest in classification["complete_frontier_hashes"]]
    excludes = set(classification["excluded_hashes"])
    unclassified = [row for row in rows.values()
                    if row["sha256"] not in excludes
                    and not any(all(leader[key] <= row[key] for key in COORDINATES)
                                for leader in frontier)]
    if unclassified:
        raise ValueError("New undominated sources need semantic review: " + repr(unclassified))
    if result["errors"]:
        raise ValueError("Source parse errors need review")
    result["frontier"] = frontier
    result["coordinate_envelope"] = {
        key: min(row[key] for row in frontier) for key in COORDINATES
    }
    result["excluded_nondominated_tooling_count"] = len(excludes)
    result["scope"] = (
        "Observed complete-source upper bounds, not lower bounds on all possible theories. "
        "Six frontier source contents and all otherwise nondominated source contents "
        "were manually reviewed. Dominated sources cannot change this frontier. "
        "No universal soundness theorem for the inherited programs is mechanically verified."
    )
    return result


def main():
    directory = Path(sys.argv[1])
    output = Path(sys.argv[2]) if len(sys.argv) > 2 else Path.cwd()
    output.mkdir(parents=True, exist_ok=True)
    result = classify(audit(directory))
    (output / "corpus_audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "python", "zlib_runtime", "root_archive_count", "unique_archive_count",
        "unique_source_count", "coordinate_envelope", "excluded_nondominated_tooling_count"
    )}, indent=2))


if __name__ == "__main__":
    main()
