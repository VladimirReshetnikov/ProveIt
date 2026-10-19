#!/usr/bin/env python3
"""Check the complete source tree and zero-padding normalization of every join.

This checks finite source structure and encoding. The logical consistency
calibration of this exact pinned source is an inherited theorem, not rerun here.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Assertions are required.")
ROOT = Path(__file__).resolve().parents[1]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sites", type=Path, default=ROOT / "machines/sites_logical.json")
    ap.add_argument("--source-dir", type=Path, default=ROOT / "reference/proveit")
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert sha256(args.sites.read_bytes()).hexdigest() == "74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d"
    rows = json.loads(args.sites.read_text())
    source_pins = {
        "ProgramRouting245.lean": "060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b",
        "ProgramRotation244.lean": "3bb25d3b5068dadd3f217b11c3fa10be0a86a5df04e3b50073413d03e8daa20a",
        "SourceRotation240.lean": "bbda8dae8ce42e890b8ad6bd8b22bf62275f0ae0114f8d2350ac558a2e5ac21b",
        "CalibratedRotation240.lean": "a3e40ae52747aa17ba03b4a3f6c935577f39fcff74ed4f158253cb48e7daf2ac",
    }
    for name, digest in source_pins.items():
        assert sha256((args.source_dir / name).read_bytes()).hexdigest() == digest
    literal = (args.source_dir / "ProgramRouting245.lean").read_text()
    dag = {}
    for index, body in re.findall(r"private def row(\d{3}) : Row := (.+)", literal):
        edges = re.findall(r"\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?", body)
        assert len(edges) == 2 and int(index) not in dag
        dag[int(index)] = tuple((op, int(value) if value else None) for op, value in edges)
    assert set(dag) == set(range(203))
    rotation244 = (args.source_dir / "ProgramRotation244.lean").read_text()
    rotation240 = (args.source_dir / "SourceRotation240.lean").read_text()
    assert "if n = 5 then (.decnz 6, .cont 2)" in rotation244
    assert "else if n = 6 then (.inc 0, .node 5)" in rotation244
    assert "else ProgramRouting245.program.nodes n" in rotation244
    assert "if n = 169 then (.inc 5, .node 5)" in rotation240
    assert "else ProgramRotation244.program.nodes n" in rotation240
    dag[5], dag[6], dag[169] = (("decnz", 6), ("cont", 2)), (("inc", 0), ("node", 5)), (("inc", 5), ("node", 5))
    expanded = []
    opcodes = {"inc": "CI", "decnz": "CD", "brk": "CB", "cont": "CC", "halt": "CH"}
    def unfold(edge, path):
        op, argument = edge
        if op == "node":
            for bit, child in enumerate(dag[argument]):
                if child[0] == "node":
                    assert child[1] < argument
                unfold(child, path + str(bit))
        else:
            expanded.append([path, opcodes[op], argument])
    unfold(("node", 202), "")
    assert expanded == rows, "Literal calibrated DAG and supplied instruction source differ."
    leaves = {p: (op, arg) for p, op, arg in rows}
    nodes = {p[:k] for p in leaves for k in range(len(p))}
    assert len(leaves) == len(rows) == 6455
    assert len(nodes) == 6454 and not nodes.intersection(leaves)
    assert all(p + b in nodes or p + b in leaves for p in nodes for b in "01")
    assert max(map(len, leaves)) == 51
    assert sum(op == "CH" for op, arg in leaves.values()) == 1
    assert all(0 <= arg < 9 for op, arg in leaves.values() if op in ("CI", "CD"))

    def first(p):
        assert p in nodes or p in leaves
        while p not in leaves:
            p += "0"
        return p

    def next_subtree(p):
        if not p:
            return ""
        if p[-1] == "0":
            return p[:-1] + "1"
        return next_subtree(p[:-1])

    def leave(p, bit, count):
        if not count or not p:
            return p
        return leave(p[:-1], bit, count - (p[-1] == bit))

    # Independent integer representation of the physical path operations.
    def increment_word(p):
        if not p:
            return "", 1
        n = int(p, 2) + 1
        return format(n % (1 << len(p)), f"0{len(p)}b"), int(n == 1 << len(p))

    def trim_word(p, bit, count):
        for i in reversed(range(len(p))):
            if p[i] == bit:
                count -= 1
                if count == 0:
                    return p[:i]
        return ""

    assert first("").strip("0") == ""
    checked = 0
    for p, op, arg in rows:
        for positive in ((False, True) if op == "CD" else (False,)):
            if op == "CH":
                checked += 1
                continue
            if op == "CI" or op == "CD" and positive:
                structured = next_subtree(p)
                physical, overflow = increment_word(p)
            elif op in ("CD", "CB"):
                count = 1 if op == "CD" else arg
                structured = next_subtree(leave(p, "0", count))
                physical, overflow = increment_word(trim_word(p, "0", count))
            else:
                assert op == "CC"
                structured = leave(p, "1", arg)
                physical, overflow = trim_word(p, "1", arg), 0
            canonical = first(structured)
            assert physical.ljust(64, "0") == canonical.ljust(64, "0"), (p, op, arg, positive)
            assert len(physical) <= 64 and overflow in (0, 1)
            checked += 1
    assert checked == 8386
    result = {
        "status": "COMPLETE_SOURCE_TREE_AND_PADDING_JOINS_PASS",
        "leaves": 6455, "internal_nodes": 6454, "maximum_depth": 51,
        "guards_including_halt": checked,
        "literal_source_dag_rows": 203,
        "all_ordered_leaves_reconstructed_from_pinned_Lean_definitions": True,
        "reference_source_pins": source_pins,
        "initial_leftmost_leaf": first(""),
        "empty_path_is_same_zero_padded_tape": True,
        "only_primary_registers_zero_through_eight_used": True,
        "calibration_scope": "Exact source identity is pinned; the prior logical calibration is an imported mathematical theorem.",
        "source_sha256": sha256(args.sites.read_bytes()).hexdigest(),
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
