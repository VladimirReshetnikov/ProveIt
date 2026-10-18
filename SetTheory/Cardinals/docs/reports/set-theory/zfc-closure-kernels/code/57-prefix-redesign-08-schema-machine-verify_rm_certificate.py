#!/usr/bin/env python3
"""Independent finite verifier for rebracket_axioms.py's RM certificate.

Uses string/integer path arithmetic, independently parses the pinned Coq data,
does not import or execute the generator or Wade backend. Checking this finite
certificate is executable evidence, not a Lean proof or a binary-TM compiler
correctness proof. All output is on stdout; the verifier writes no files.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import cache
import hashlib
import json
from pathlib import Path
import re

SOURCE_SHA256 = "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3"
JSON_SHA256 = "bb884eacd778c79f4cc672ea4136db91e7d4ad7eb70ead7cc2892aba56566db5"


class Machine:
    def __init__(self, rows):
        self.rows = rows
        assert set(rows) == set(range(len(rows)))
        for edges in rows.values():
            assert len(edges) == 2
            for e in edges:
                m = re.fullmatch(r"(ENode|EInc|EDecnz|EBreak|EContinue) (\d+)|EHalt", e)
                assert m is not None
                if e.startswith("ENode "):
                    assert int(e[6:]) in rows

    @cache
    def lookup(self, pc):
        state, cursor, actual = 0, 0, ""
        while cursor <= len(self.rows):
            bit = pc[cursor] if cursor < len(pc) else "0"
            actual += bit
            edge = self.rows[state][int(bit)]
            if not edge.startswith("ENode "):
                return actual, edge
            state = int(edge[6:])
            cursor += 1
        raise AssertionError("decoder cycle")

    @staticmethod
    def successor(pc):
        if not pc:
            return ""
        return format((int(pc, 2) + 1) % (1 << len(pc)), f"0{len(pc)}b")

    @staticmethod
    def remove(pc, bit, n):
        for _ in range(n):
            pos = pc.rfind(bit)
            if pos < 0:
                return ""
            pc = pc[:pos]
        return pc

    @cache
    def contract(self, pc):
        seen = set()
        while True:
            path, edge = self.lookup(pc)
            if edge == "EHalt" or edge.startswith("EInc ") or edge.startswith("EDecnz "):
                return path, edge
            assert path not in seen, "control-only cycle"
            seen.add(path)
            kind, arg = edge.split()
            if kind == "EBreak":
                pc = self.successor(self.remove(path, "0", int(arg)))
            elif kind == "EContinue":
                pc = self.remove(path, "1", int(arg))
            else:
                raise AssertionError("unsupported instruction")

    def targets(self, path, edge):
        if edge == "EHalt":
            return []
        pos = self.contract(self.successor(path))
        if edge.startswith("EInc "):
            return [pos]
        assert edge.startswith("EDecnz ")
        zero = self.contract(self.successor(self.remove(path, "0", 1)))
        return [zero, pos]


def verify(source: Path, candidate: Path, certificate: Path):
    raw = source.read_bytes()
    if source.suffix == ".json":
        assert hashlib.sha256(raw).hexdigest() == JSON_SHA256
        original = json.loads(raw)
        assert original["source_sha256"] == SOURCE_SHA256 and original["root"] == 0
        oldrows = {int(n): tuple(es) for n, es in original["nodes"].items()}
    else:
        assert hashlib.sha256(raw).hexdigest() == SOURCE_SHA256
        matches = re.findall(r"^  \| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)",
                             raw.decode(), flags=re.M)
        oldrows = {int(n): (a, b) for n, a, b in matches}
        assert len(matches) == len(oldrows)
    assert len(oldrows) == 219
    data = json.loads(candidate.read_text())
    assert data["root"] == 0
    newrows = {int(n): tuple(es) for n, es in data["nodes"].items()}
    old, new = Machine(oldrows), Machine(newrows)
    cert = json.loads(certificate.read_text())
    records = cert["pairs"]
    assert cert["initial"] == 0
    assert cert["branch_order"] == "EDecnz: zero, positive"
    assert old.contract("") == (records[0]["old"], records[0]["instruction"])
    assert new.contract("") == (records[0]["new"], records[0]["instruction"])
    distinct = set()
    for record in records:
        left, right, label = record["old"], record["new"], record["instruction"]
        assert (left, right) not in distinct
        distinct.add((left, right))
        assert old.lookup(left) == (left, label)
        assert new.lookup(right) == (right, label)
        successors = record["successors"]
        left_targets, right_targets = old.targets(left, label), new.targets(right, label)
        assert len(successors) == len(left_targets) == len(right_targets)
        for index, a, b in zip(successors, left_targets, right_targets, strict=True):
            assert type(index) is int and 0 <= index < len(records)
            target = records[index]
            assert a == (target["old"], target["instruction"])
            assert b == (target["new"], target["instruction"])
    reachable, pending = set(), [0]
    while pending:
        index = pending.pop()
        if index in reachable:
            continue
        reachable.add(index)
        pending.extend(records[index]["successors"])
    assert len(reachable) == len(records)
    return {"verified": True, "pairs": len(records), "old_nodes": len(oldrows),
            "new_nodes": len(newrows),
            "labels": dict(Counter(r["instruction"].split()[0] for r in records)),
            "source_sha256": SOURCE_SHA256,
            "candidate_sha256": hashlib.sha256(candidate.read_bytes()).hexdigest(),
            "certificate_sha256": hashlib.sha256(certificate.read_bytes()).hexdigest(),
            "formalized_in_Lean": False, "binary_TM_correctness_proved": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(verify(args.source, args.candidate, args.certificate), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
