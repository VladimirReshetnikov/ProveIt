#!/usr/bin/env python3
"""Check a finite compiler map in Wade's zero-padded RegisterPath semantics.

Input is a JSON list of [binary_leaf_address, opcode, argument].  The opcodes
are CI/CD (register increment/decrement), CB/CC (break/continue), and CH.
This independent checker validates a complete binary prefix tree, constructs
its explicit leaf control-flow graph, and checks an optional site map between
two programs.  It has no dependence on a binary-TM simulation engine.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path


def digest(obj):
    return sha256(json.dumps(obj, separators=(",", ":"), sort_keys=True).encode()).hexdigest()


def increment(word: str) -> str:
    if not word:
        return ""
    return format((int(word, 2) + 1) % (1 << len(word)), f"0{len(word)}b")


def strip(word: str, bit: str, count: int) -> str:
    if count < 0:
        raise ValueError("Negative strip count")
    position = len(word)
    while count and position:
        position -= 1
        if word[position] == bit:
            count -= 1
    return word[:position]


class Program:
    def __init__(self, sites):
        self.sites = [tuple(row) for row in sites]
        self.by_address = {}
        trie = {}
        for address, op, argument in self.sites:
            if not address or any(x not in "01" for x in address):
                raise ValueError(f"Invalid leaf address {address!r}")
            if address in self.by_address:
                raise ValueError(f"Duplicate leaf {address}")
            if op not in {"CI", "CD", "CB", "CC", "CH"}:
                raise ValueError(f"Invalid opcode {op}")
            if op == "CH":
                if argument is not None:
                    raise ValueError("Halt must have null argument")
            elif not isinstance(argument, int) or argument < 0:
                raise ValueError("Instruction argument must be natural")
            self.by_address[address] = (op, argument)
            current = trie
            for bit in address:
                if "leaf" in current:
                    raise ValueError("Leaf is prefix of another leaf")
                current = current.setdefault(bit, {})
            if current:
                raise ValueError("Leaf is prefix of another leaf")
            current["leaf"] = address
        pending = [trie]
        while pending:
            node = pending.pop()
            if "leaf" in node:
                if set(node) != {"leaf"}:
                    raise ValueError("Malformed leaf")
            else:
                if set(node) != {"0", "1"}:
                    raise ValueError("Incomplete binary prefix tree")
                pending.extend([node["0"], node["1"]])
        self.trie = trie
        self.initial = self.decode("")

    def decode(self, word: str) -> str:
        current = self.trie
        position = 0
        while "leaf" not in current:
            current = current[word[position] if position < len(word) else "0"]
            position += 1
        return current["leaf"]

    def signature(self, address):
        op, argument = self.by_address[address]
        if op in {"CI", "CD"}:
            return op, argument
        return ("halt", None) if op == "CH" else ("jump", None)

    def successors(self, address):
        op, argument = self.by_address[address]
        if op == "CH":
            return {}
        if op == "CI":
            return {"always": self.decode(increment(address))}
        if op == "CD":
            return {"positive": self.decode(increment(address)),
                    "zero": self.decode(increment(strip(address, "0", 1)))}
        if op == "CB":
            return {"always": self.decode(increment(strip(address, "0", argument)))}
        return {"always": self.decode(strip(address, "1", argument))}

    def graph(self):
        return {address: {"effect": self.signature(address), "successors": self.successors(address)}
                for address in sorted(self.by_address)}


def check_map(source: Program, target: Program, mapping: dict[str, str]):
    if set(mapping) != set(source.by_address):
        raise ValueError("Mapping domain is not the complete source leaf set")
    if not set(mapping.values()) <= set(target.by_address):
        raise ValueError("Mapping contains nonexistent target leaves")
    if mapping[source.initial] != target.initial:
        raise ValueError("Initial leaf is not preserved")
    failures = []
    guards = 0
    for address in sorted(source.by_address):
        image = mapping[address]
        if source.signature(address) != target.signature(image):
            failures.append({"source": address, "image": image, "reason": "register effect or halt tag differs"})
            continue
        expected = {guard: mapping[value] for guard, value in source.successors(address).items()}
        actual = target.successors(image)
        guards += 2 if source.signature(address)[0] == "CD" else 1
        if expected != actual:
            failures.append({"source": address, "image": image, "reason": "successor does not commute",
                             "expected": expected, "actual": actual})
    return {"status": "PASS" if not failures else "FAIL", "source_leaves": len(source.sites),
            "target_leaves": len(target.sites), "guarded_cases": guards,
            "source_sites_sha256": digest(source.sites), "target_sites_sha256": digest(target.sites),
            "mapping_sha256": digest(mapping), "failures": failures,
            "claim": "Exact finite leaf-graph map with identical register effects and halting tags",
            "scope": "Compiler/RegisterPath equivalence only; no binary-TM or bootstrap certificate"}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("source")
    ap.add_argument("target", nargs="?")
    ap.add_argument("--mapping", help="JSON source-address to target-address map; default is leaf order")
    ap.add_argument("--output")
    args = ap.parse_args()
    source = Program(json.loads(Path(args.source).read_text()))
    target = Program(json.loads(Path(args.target or args.source).read_text()))
    if args.mapping:
        mapping = json.loads(Path(args.mapping).read_text())
    else:
        if len(source.sites) != len(target.sites):
            ap.error("Default leaf-order mapping requires equal leaf counts")
        mapping = dict(zip(sorted(source.by_address), sorted(target.by_address)))
    result = check_map(source, target, mapping)
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(output)
    print(output, end="")
    raise SystemExit(0 if result["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
