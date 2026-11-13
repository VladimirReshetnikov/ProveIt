"""Offline byte-identity and size remeasurement of every inspected source.

Upstream programs are parsed but NEVER executed. Compressed archival Python
sources are decompressed before normalization; runtime exec wrappers remain
wrappers and are excluded from the direct-checker comparison.
"""
import ast
import gzip
import hashlib
import io
import json
from pathlib import Path
import tokenize

ROOT = Path(__file__).resolve().parents[1]
SKIP = {tokenize.ENCODING, tokenize.ENDMARKER, tokenize.NEWLINE, tokenize.NL,
        tokenize.INDENT, tokenize.DEDENT, tokenize.COMMENT}


def main():
    report = json.loads((ROOT / "evidence/artifacts_source_census.json").read_text())
    count = 0
    inventory = hashlib.sha256()
    for row in sorted(report["sources"], key=lambda value: value["git_sha"]):
        raw = (ROOT / "reference/source_corpus" / row["git_sha"]).read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
        if actual != row["git_sha"]:
            raise ValueError("Git identity mismatch: " + row["git_sha"])
        source = gzip.decompress(raw) if raw[:2] == b"\x1f\x8b" else raw
        digest = hashlib.sha256(source).hexdigest()
        if digest != row["source_sha256"]:
            raise ValueError("Source identity mismatch: " + row["git_sha"])
        parsed = ast.parse(source.decode("utf-8-sig"))
        normalized = ast.unparse(parsed) + "\n"
        metrics = {
            "tokens": sum(t.type not in SKIP for t in tokenize.generate_tokens(io.StringIO(normalized).readline)),
            "ast_nodes": len(list(ast.walk(parsed))),
            "normalized_bytes": len(normalized.encode()),
        }
        for key, value in metrics.items():
            if value != row[key]:
                raise ValueError("Source metric mismatch: " + row["git_sha"] + " / " + key)
        inventory.update((row["git_sha"] + " " + digest + "\n").encode())
        count += 1
    summary = json.loads((ROOT / "evidence/census_summary.json").read_text())
    if inventory.hexdigest() != summary["source_inventory_digest_sha256"]:
        raise ValueError("Source inventory digest mismatch")
    print(json.dumps({"source_paths": report["path_count"], "verified_unique_blobs": count,
                      "programs_executed": 0, "inventory_sha256": inventory.hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
