"""Reproduce the pinned complete-checker frontier entirely from bundled ZIPs.

Manual semantic classifications are read from corpus_classification.json.
This script verifies their coverage; it does not infer proof-checker validity
from a short source file, a filename, or a successful finite test.
"""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize
import zipfile

ROOT = Path(__file__).resolve().parent.parent
IGNORED = {tokenize.ENCODING, tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
           tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
COORDINATES = ("tokens", "ast", "bytes")


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


def source_metrics(raw, path):
    source = raw.decode("utf-8")
    tree = ast.fix_missing_locations(StripDocstrings().visit(ast.parse(source)))
    normalized = ast.unparse(tree) + "\n"
    return {
        "path": path,
        "sha256": hashlib.sha256(raw).hexdigest(),
        "tokens": sum(token.type not in IGNORED for token in
                      tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast": sum(1 for _ in ast.walk(tree)),
        "bytes": len(normalized.encode("utf-8")),
        "raw_bytes": len(raw),
        "has_public_json_input": ("load(open(0))" in normalized
                                  or "loads(input(" in normalized),
        "has_accept": "ACCEPT" in normalized,
        "has_reject": "REJECT" in normalized,
    }


def scan_zip(raw, path, rows, errors):
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        for name in archive.namelist():
            if name.endswith(".zip"):
                scan_zip(archive.read(name), path + "!" + name, rows, errors)
            elif name.endswith(".py"):
                member = path + "!" + name
                try:
                    rows.append(source_metrics(archive.read(name), member))
                except Exception as error:
                    errors.append({"path": member, "error": str(error)})


def main():
    original = json.loads((ROOT / "evidence/current_corpus_metrics.json").read_text())
    classification = json.loads((ROOT / "evidence/corpus_classification.json").read_text())
    if classification["commit"] != original["commit"]:
        raise ValueError("Classification and source snapshot commits differ")
    expected_names = sorted(item["name"] for item in original["archives"])
    actual_names = sorted(path.name for path in (ROOT / "sources").glob("*.zip"))
    if actual_names != expected_names:
        raise ValueError("Bundled source archive inventory differs from the snapshot")

    rows, errors, identities = [], [], []
    for item in original["archives"]:
        raw = (ROOT / "sources" / item["name"]).read_bytes()
        identity = {
            "name": item["name"], "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
            "git_blob_sha1": hashlib.sha1(
                b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest(),
        }
        if identity != item:
            raise ValueError("Bundled archive identity differs: " + item["name"])
        identities.append(identity)
        scan_zip(raw, item["name"], rows, errors)
    if errors:
        raise ValueError("Source parsing failed: " + json.dumps(errors))

    semantic = classification["semantic_classification"]
    threshold = semantic["complete_checker_envelope"]
    excluded = {item["sha256"]: item for item in semantic["excluded_small_sources"]}
    known_attainers = {item["sha256"]: item
                      for item in classification["complete_attaining_sources"]}
    by_hash = {row["sha256"]: row for row in rows}
    for digest, reviewed in {**excluded, **known_attainers}.items():
        if digest not in by_hash:
            raise ValueError("A manually reviewed source is absent: " + digest)
        if any(by_hash[digest][key] != reviewed[key] for key in COORDINATES):
            raise ValueError("Reviewed source metrics changed: " + digest)

    # Every source that could improve any coordinate must have a semantic
    # classification. The pinned audit found only the fourteen non-checkers.
    under_envelope = {
        row["sha256"] for row in rows
        if any(row[key] < threshold[key] for key in COORDINATES)
    }
    unreviewed = under_envelope - set(excluded) - set(known_attainers)
    if unreviewed:
        raise ValueError("Unreviewed under-envelope sources: " + repr(sorted(unreviewed)))

    candidates = [row for row in rows if row["has_public_json_input"]
                  and row["has_accept"] and row["sha256"] not in excluded]
    envelope = {key: min(row[key] for row in candidates) for key in COORDINATES}
    attainers = {key: [row for row in candidates if row[key] == envelope[key]]
                 for key in COORDINATES}
    if any(row["sha256"] not in known_attainers
           for group in attainers.values() for row in group):
        raise ValueError("An apparent frontier attainer lacks semantic review")
    if envelope != threshold:
        raise ValueError("Reproduced envelope differs from the manually audited result")
    unique_count = len(by_hash)
    if len(rows) != original["source_occurrences"] or unique_count != original["unique_source_hashes"]:
        raise ValueError("Reproduced source counts differ from the original scan")

    result = {
        "commit": original["commit"],
        "python": platform.python_version(),
        "archive_count": len(identities), "archives": identities,
        "source_occurrences": len(rows), "unique_source_hashes": unique_count,
        "parse_errors": errors,
        "complete_checker_envelope": envelope, "attainers": attainers,
        "manual_excluded_small_source_count": len(excluded),
        "under_envelope_distinct_source_count": len(under_envelope),
        "all_under_envelope_sources_classified": not unreviewed,
        "semantic_classification_file": "evidence/corpus_classification.json",
        "scope": "Pinned finite-corpus upper bounds, not absolute minimality; validity classification is an explicitly preserved manual review",
        "rows": rows,
    }
    output = ROOT / "evidence/reproduced_corpus_metrics.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in (
        "commit", "python", "archive_count", "source_occurrences",
        "unique_source_hashes", "complete_checker_envelope",
        "manual_excluded_small_source_count", "all_under_envelope_sources_classified")}, indent=2))


if __name__ == "__main__":
    main()
