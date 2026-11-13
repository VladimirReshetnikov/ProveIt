#!/usr/bin/env python3
"""Measure unchanged complete controls. No proof-checker code is executed."""
import ast
import hashlib
import io
import json
from pathlib import Path
import platform
import tokenize

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    "stream_tokens239.py": (239, 261, 549),
    "stream_ast256.py": (245, 256, 580),
    "shifted_bytes461.py": (267, 298, 461),
    "checker_strict_tokens317.py": (317, 368, 634),
    "checker_strict_ast356.py": (325, 356, 646),
    "checker_strict597.py": (328, 372, 597),
}
IGNORED = {
    tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
    tokenize.DEDENT, tokenize.ENDMARKER, tokenize.COMMENT,
}


def measure(data):
    tree = ast.parse(data.decode("utf-8"))
    normalized = ast.unparse(tree) + "\n"
    normalized_tree = ast.parse(normalized)
    return {
        "significant_tokens": sum(t.type not in IGNORED for t in
                                  tokenize.generate_tokens(io.StringIO(normalized).readline)),
        "ast_nodes": sum(1 for _ in ast.walk(normalized_tree)),
        "normalized_bytes": len(normalized.encode("utf-8")),
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized.encode("utf-8")).hexdigest(),
    }


def main():
    provenance = json.loads((ROOT / "evidence/controls_provenance.json").read_text())
    rows = []
    for item in provenance["sources"]:
        path = ROOT / item["local_file"]
        row = {"file": item["local_file"], **measure(path.read_bytes())}
        if row["source_sha256"] != item["sha256"]:
            raise ValueError("Source hash mismatch: " + str(path))
        actual = tuple(row[k] for k in
                       ("significant_tokens", "ast_nodes", "normalized_bytes"))
        row["matches_recorded_coordinates"] = actual == EXPECTED[path.name]
        if platform.python_version() == "3.12.14" and not row["matches_recorded_coordinates"]:
            raise ValueError("Measurement mismatch: " + str(path))
        rows.append(row)
    result = {
        "python": platform.python_version(),
        "commit": provenance["commit"],
        "method": "ast.unparse(ast.parse(source)) + newline; complete modules",
        "all_source_hashes_verified": True,
        "all_coordinates_match": all(r["matches_recorded_coordinates"] for r in rows),
        "measurements": rows,
        "limitations": "Source measurement only; does not prove checker soundness or minimality.",
    }
    destination = ROOT / "evidence/reproduced_metrics.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
