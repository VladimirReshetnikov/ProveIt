#!/usr/bin/env python3
"""Reproduce textual metrics; Lean validation is recorded separately."""

import argparse
import collections
import hashlib
import json
import re
from pathlib import Path


def public_headers(source: str) -> dict[str, str]:
    result = {}
    for match in re.finditer(r"^(?:theorem|def) (\w+)\b", source, re.M):
        end = source.index(":=", match.start())
        result[match.group(1)] = " ".join(source[match.start():end].split())
    return result


def digest(source: str) -> str:
    return hashlib.sha256(source.encode()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    args = parser.parse_args()
    relative = Path("Computability/DiophantineConsistency/Lean/DiophantineConsistency")
    original = (args.repository / relative / "NativeCoefficientBounds.lean").read_text()
    candidate = args.candidate.read_text()
    parent = (args.repository / relative / "NativeQuadraticParent.lean").read_text()
    begin = parent.index("def rowCoefficient")
    end = parent.index("/-- The actual source supports", begin)
    expressions = re.findall(r" then (.*?) else ", parent[begin:end])
    counts = collections.Counter(expressions)
    region_begin = original.index("private theorem rowEnvelope_0")
    region_end = original.index("/-- The exact height required", region_begin)
    region = original[region_begin:region_end]
    old_headers, new_headers = public_headers(original), public_headers(candidate)
    assert old_headers == new_headers, "A public declaration header has changed"
    print(json.dumps({
        "baseline_commit": "60e9c5d620c6c387d932876cfa2d9376f64ea56c",
        "path": str(relative / "NativeCoefficientBounds.lean"),
        "baseline_sha256": digest(original),
        "candidate_sha256": digest(candidate),
        "baseline_lines": len(original.splitlines()),
        "candidate_lines": len(candidate.splitlines()),
        "baseline_bytes": len(original.encode()),
        "candidate_bytes": len(candidate.encode()),
        "public_declaration_headers_identical": True,
        "public_declaration_names": list(old_headers),
        "private_row_lemmas": region.count("private theorem rowEnvelope_"),
        "repeated_linarith_leaf_calls": region.count("linarith only"),
        "repeated_abs_ite_applications": region.count("apply abs_ite_le"),
        "row_lemma_and_dispatch_region_lines": len(region.splitlines()),
        "coefficient_catalog": {
            "nondefault_branches": len(expressions),
            "distinct_textual_nondefault_values": len(counts),
            "default_value": "0",
            "branch_counts_by_expression": dict(counts.most_common()),
            "scope": "textual expressions in the literal rowCoefficient definition",
        },
        "metric_scope": "source text only; not proof-term size or compile speed",
    }, indent=2))


if __name__ == "__main__":
    main()
