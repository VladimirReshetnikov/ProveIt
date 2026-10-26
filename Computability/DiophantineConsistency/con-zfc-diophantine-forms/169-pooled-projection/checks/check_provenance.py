#!/usr/bin/env python3
"""Authenticate the retained repository inputs and the comparison polynomial."""
from collections import defaultdict
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def check():
    ledger = json.loads((ROOT / "provenance/SOURCES.json").read_text())
    require(ledger["commit"] == "953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4", "pinned commit")
    for record in ledger["retained_imports"]:
        path = ROOT / record["local_path"]
        require(path.resolve().is_relative_to(ROOT), "relative import path")
        data = path.read_bytes()
        require(len(data) == record["bytes"], "byte count: " + record["local_path"])
        require(hashlib.sha256(data).hexdigest() == record["sha256"],
                "SHA256: " + record["local_path"])
        git = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(git == record["git_blob_sha1"], "Git blob: " + record["local_path"])
    source = json.loads((ROOT / "comparisons/source158_P225.json").read_text())
    require(len(source["variables"]) == 225 and len(source["residuals"]) == 162,
            "comparison variable/row counts")
    expansion = defaultdict(int)
    for row in source["residuals"]:
        for c, m in row["terms"]:
            for d, n in row["terms"]:
                expansion[tuple(sorted(m + n))] += c * d
    expansion = {m: c for m, c in expansion.items() if c}
    comparison = {"variables": 225, "rows": 162, "degree": max(map(len, expansion)),
                  "monomials": len(expansion), "height": max(map(abs, expansion.values()))}
    require(comparison == {"variables": 225, "rows": 162, "degree": 4,
                           "monomials": 7867, "height": 128446}, "literal comparison metrics")
    return {"status": "passed", "byte_exact_repository_files": len(ledger["retained_imports"]),
            "repository_commit": ledger["commit"], "source158_comparison": comparison}

if __name__ == "__main__":
    print(json.dumps(check(), indent=2, sort_keys=True))
