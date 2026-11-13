#!/usr/bin/env python3
"""Read-only Python-source census; inspected source is never executed."""
import argparse
import ast
from collections import Counter
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zipfile

IGNORED_TOKENS = {
    tokenize.ENCODING, tokenize.ENDMARKER, tokenize.COMMENT,
    tokenize.NEWLINE, tokenize.NL, tokenize.INDENT, tokenize.DEDENT,
}
SUBTREE = Path("Logic/PrimitiveRecursiveArithmetic/ConciseIPRA")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="ProveIt checkout or ConciseIPRA subtree")
    parser.add_argument("--output", type=Path, default=Path("census.json"))
    parser.add_argument("--commit", default=None, help="Recorded source commit, supplied by the caller")
    parser.add_argument("--archive-depth", type=int, default=5)
    args = parser.parse_args()
    root = args.source / SUBTREE if (args.source / SUBTREE).is_dir() else args.source
    if not root.is_dir():
        parser.error("source directory does not exist")
    counts = Counter()
    rows = {}
    errors = []

    def inspect(name, data, depth=0):
        if name.endswith(".zip"):
            if depth >= args.archive_depth:
                counts["archive_depth_omissions"] += 1
                return
            counts["archives"] += 1
            try:
                with zipfile.ZipFile(io.BytesIO(data)) as archive:
                    for member in sorted(archive.namelist()):
                        if member.endswith((".py", ".py.gz", ".zip")):
                            inspect(name + "!" + member, archive.read(member), depth + 1)
            except Exception as error:
                errors.append({"path": name, "stage": "archive", "error": str(error)})
            return
        if name.endswith(".py.gz"):
            try:
                data = gzip.decompress(data)
            except Exception as error:
                errors.append({"path": name, "stage": "gzip", "error": str(error)})
                return
        if not name.endswith((".py", ".py.gz")):
            return
        counts["python_occurrences"] += 1
        try:
            tree = ast.parse(data)
            normalized = ast.unparse(tree) + "\n"
        except Exception as error:
            errors.append({"path": name, "stage": "parse", "error": str(error)})
            return
        digest = hashlib.sha256(normalized.encode()).hexdigest()
        if digest in rows:
            rows[digest]["paths"].append(name)
            return
        tokens = tokenize.generate_tokens(io.StringIO(normalized).readline)
        rows[digest] = {
            "paths": [name],
            "tokens": sum(token.type not in IGNORED_TOKENS for token in tokens),
            "ast_nodes": sum(1 for _ in ast.walk(tree)),
            "normalized_bytes": len(normalized.encode()),
            "normalized_gzip9_bytes": len(gzip.compress(normalized.encode(), compresslevel=9, mtime=0)),
            "accept_literal": "ACCEPT" in normalized,
            "dynamic_code_call": any(
                isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id in {"exec", "eval", "compile"}
                for node in ast.walk(tree)
            ),
        }

    for path in sorted(root.rglob("*")):
        if path.is_file() and path.name.endswith((".py", ".py.gz", ".zip")):
            inspect(path.relative_to(root).as_posix(), path.read_bytes())
    candidates = [
        {"normalized_sha256": digest, **row}
        for digest, row in rows.items()
        if (row["accept_literal"] or row["dynamic_code_call"])
        and (row["tokens"] < 239 or row["ast_nodes"] < 256 or row["normalized_bytes"] < 461)
    ]
    report = {
        "source_root_name": root.name,
        "caller_supplied_commit": args.commit,
        "python_version": platform.python_version(),
        "counts": dict(counts),
        "unique_normalized_modules": len(rows),
        "errors": errors,
        "candidate_filter": {
            "coordinate_thresholds": {"tokens": 239, "ast_nodes": 256, "normalized_bytes": 461},
            "meaning": "Below at least one coordinate and containing ACCEPT or a dynamic-code call; search aid only, not qualification.",
        },
        "below_threshold_candidates": candidates,
        "modules": rows,
        "limits": [
            "No inspected source is imported or executed.",
            "Candidate classification, soundness, and completeness require separate mathematical review.",
            "Packed execution wrappers, builders, runners, and unsound mutants can pass the syntactic filter.",
            "This is a finite source census and not a global simplicity lower-bound proof.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "counts": dict(counts), "unique_normalized_modules": len(rows),
        "errors": len(errors), "below_threshold_candidates": len(candidates),
    }, indent=2))


if __name__ == "__main__":
    main()
