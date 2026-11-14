#!/usr/bin/env python3
"""Check an invariant certificate, independently of its worklist generator.

Uses the sibling core.py only for parsing the pinned source instruction array.
Does not recompute reachability, so accidental omission of a successor fails.
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "verification"))
from core import program


def main():
    source = ROOT / "inputs/pa196/PA196/Program.lean"
    certificate = ROOT / "verification/zero_invariants.json"
    sites, instructions = program()
    masks = list(map(int, json.loads(certificate.read_text())["reachable_masks"]))
    assert len(masks) == len(instructions) == 3812
    assert all(0 <= bitset < (1 << 512) for bitset in masks)
    assert (masks[25] >> 1) & 1
    edges = 0
    states = 0
    for pc, bitset in enumerate(masks):
        for mask in range(512):
            if not (bitset >> mask) & 1:
                continue
            states += 1
            op = instructions[pc]
            if op[0] == "halt":
                successors = []
            elif op[0] == "jump":
                successors = [(op[1], mask)]
            elif op[0] == "inc":
                successors = [(op[2], mask | (1 << op[1]))]
            elif op[0] == "dec":
                bit = 1 << op[1]
                successors = ([(op[3], mask), (op[3], mask & ~bit)]
                              if mask & bit else [(op[2], mask)])
            else:
                raise AssertionError(op)
            for dest, new_mask in successors:
                assert 0 <= dest < len(masks)
                assert (masks[dest] >> new_mask) & 1, (pc, mask, dest, new_mask)
                edges += 1
    result = {
        "ok": True,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest(),
        "sites": len(masks),
        "site_pattern_pairs": states,
        "checked_edges": edges,
        "initial_site": 25,
        "initial_pattern": 1,
        "claim": "Contains startup pattern and is closed under every abstract source successor.",
    }
    path = Path(__file__).with_name("zero_invariant_check.json")
    path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
