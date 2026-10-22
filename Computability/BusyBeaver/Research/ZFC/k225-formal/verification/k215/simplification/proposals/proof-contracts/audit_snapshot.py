#!/usr/bin/env python3
"""Reproduce the finite source census; this is not a proof-assistant check."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def audit(root: Path = BASE) -> dict:
    if not __debug__:
        raise RuntimeError("Run without -O; this finite audit uses assertions.")
    pins = json.loads((root / "baseline/pins.json").read_text())
    for item in pins["files"]:
        p = root / "baseline" / item["local"]
        data = p.read_bytes()
        assert sha256(data) == item["sha256"], f"Input mismatch: {p}"
        assert len(data) == item["bytes"], f"Size mismatch: {p}"
    sites = json.loads((root / "baseline/sites215.json").read_text())
    trie: dict = {}
    for word, opcode, arg in sites:
        assert word and set(word) <= {"0", "1"}
        assert opcode in {"CI", "CD", "CB", "CC", "CH"}
        if opcode in {"CI", "CD"}:
            assert isinstance(arg, int) and 0 <= arg < 9
        elif opcode == "CH":
            assert arg is None
        else:
            assert isinstance(arg, int) and arg >= 0
        node = trie
        for bit in word:
            assert "leaf" not in node, "A source word extends a leaf"
            node = node.setdefault(bit, {})
        assert not node, "Duplicate word or a leaf prefixes another word"
        node["leaf"] = (opcode, arg)
    shapes = set()

    def shape(node: dict) -> tuple:
        if "leaf" in node:
            assert set(node) == {"leaf"}
            result = ("leaf",) + node["leaf"]
        else:
            assert set(node) == {"0", "1"}, "Source is not a complete binary tree"
            result = ("fork", shape(node["0"]), shape(node["1"]))
        shapes.add(result)
        return result

    shape(trie)
    rows = []
    for line in (root / "baseline/k215.tm").read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        assert len(parts) == 5, f"Malformed table row: {line}"
        q, read, write, direction, target = parts
        row = (int(q), int(read), int(write), direction, int(target))
        assert 0 <= row[0] < 215 and row[1] in (0, 1)
        assert row[2] in (0, 1) and row[3] in ("L", "R")
        assert 0 <= row[4] <= 215
        rows.append(row)
    assert len(rows) == 430
    assert {(q, b) for q, b, *_ in rows} == {(q, b) for q in range(215) for b in (0, 1)}
    counts = Counter(opcode for _, opcode, _ in sites)
    branch_count = sum(2 if opcode == "CD" else 1 for _, opcode, _ in sites)
    prefix_sum = sum(len(word) - 1 for word, _, _ in sites)
    weighted = sum((len(word) - 1) * (2 if opcode == "CD" else 1)
                   for word, opcode, _ in sites)
    return {
        "status": "PASS_FINITE_SOURCE_CENSUS",
        "snapshot": pins["commit"],
        "dense_machine_sha256": sha256((root / "baseline/k215.tm").read_bytes()),
        "sites_sha256": sha256((root / "baseline/sites215.json").read_bytes()),
        "working_states": 215,
        "binary_actions": len(rows),
        "complete_prefix_free_source": True,
        "leaf_occurrences": len(sites),
        "opcode_occurrences": dict(sorted(counts.items())),
        "branch_outcomes": branch_count,
        "distinct_primitive_kinds": len({(op, arg) for _, op, arg in sites}),
        "distinct_source_subtrees": len(shapes),
        "word_length_min": min(len(word) for word, _, _ in sites),
        "word_length_max": max(len(word) for word, _, _ in sites),
        "sum_prefix_lengths": prefix_sum,
        "branch_weighted_prefix_lengths": weighted,
        "sum_of_prefix_theorem_lower_bounds": weighted,
        "sum_of_prefix_theorem_upper_bounds": 7 * weighted,
        "scope": "Finite input audit and arithmetic census only. The two prefix bounds use the inherited mathematical theorem |pre| <= steps <= 7*|pre|. They do not measure symbolic-executor work, Lean kernel work, memory, or compile-time savings.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="compare with delivered evidence/census.json")
    args = parser.parse_args()
    result = audit()
    if args.check:
        expected = json.loads((BASE / "evidence/census.json").read_text())
        assert result == expected, "Delivered census differs from recomputation"
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
