#!/usr/bin/env python3
"""Independent binary-tree expansion and interval-based jump resolver.

Takes the delivered QN source DAG and Q grammar.  Reproduces QN literally;
restores its original dummy-push MP to construct Q-push; then applies the
same two SUMS node substitutions to reconstruct the two new source graphs.
No compiler, builder, or physical simulator is imported.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expand(nodes, grammar):
    sites = []
    intervals = {}

    def walk(term, address):
        start = len(sites)
        while isinstance(term, str):
            if term == "x67":
                term = grammar["root"]
            elif term in grammar["rules"]:
                term = grammar["rules"][term]
            else:
                term = nodes[term]
        if term[0] == "leaf":
            sites.append([list(address), term[1], term[2]])
        else:
            assert len(term) == 2
            walk(term[0], address + (0,))
            walk(term[1], address + (1,))
        intervals[address] = (start, len(sites))

    walk("node172", ())

    def cut(address, bit, occurrence):
        for i in range(len(address) - 1, -1, -1):
            if address[i] == bit:
                occurrence -= 1
                if occurrence == 0:
                    return address[:i]
        raise AssertionError("source jump escapes the tree")

    def after(address):
        # The interval immediately following a subtree is the first leaf
        # in its nearest ancestor's right sibling.
        assert address in intervals
        endpoint = intervals[address][1]
        assert endpoint < len(sites)
        return endpoint

    code = []
    for address, op, arg in sites:
        address = tuple(address)
        if op == "inc":
            ins = [op, arg, after(address)]
        elif op == "dec":
            ins = [op, arg, after(cut(address, 0, 1)), after(address)]
        elif op == "breakTo":
            ins = ["jump", after(cut(address, 0, arg))]
        elif op == "continueTo":
            ins = ["jump", intervals[cut(address, 1, arg)][0]]
        else:
            assert op == "halt"
            ins = [op]
        code.append(ins)
    return sites, code


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("nodes", type=Path)
    ap.add_argument("grammar", type=Path)
    ap.add_argument("qn_instructions", type=Path)
    ap.add_argument("qns_instructions", type=Path)
    ap.add_argument("qs_instructions", type=Path)
    ap.add_argument("output_directory", type=Path)
    args = ap.parse_args()
    base = json.loads(args.nodes.read_text())
    grammar = json.loads(args.grammar.read_text())
    assert base["node163"] == ["node6", "node54"]
    assert base["node168"] == ["node37", "node57"]
    assert base["node171"] == ["node170", "node23"]
    result = {}
    args.output_directory.mkdir(parents=True, exist_ok=True)
    for name, nopush, symmetric, supplied in (
        ("QN", True, False, args.qn_instructions),
        ("Qpush", False, False, None),
        ("QNS", True, True, args.qns_instructions),
        ("QS", False, True, args.qs_instructions),
    ):
        nodes = copy.deepcopy(base)
        if not nopush:
            nodes["node163"] = ["node6", "node55"]
        if symmetric:
            nodes["node168"] = ["node37", "node56"]
            nodes["node171"] = ["node170", [["leaf", "inc", 5], ["leaf", "continueTo", 3]]]
        sites, code = expand(nodes, grammar)
        if supplied:
            assert code == json.loads(supplied.read_text())
        target = args.output_directory / (name + "_instructions.json")
        target.write_text(json.dumps(code, indent=2) + "\n")
        result[name] = {"sites": len(sites), "sha256": digest(target),
                        "matches_supplied": supplied is not None,
                        "node163": nodes["node163"], "symmetric_sum_guard": symmetric}
    result["inputs"] = {str(p): digest(p) for p in (args.nodes, args.grammar,
                                                    args.qn_instructions,
                                                    args.qns_instructions,
                                                    args.qs_instructions)}
    result["scope"] = "Independent source expansion and ordinal-interval jump resolution; no physical simulation."
    (args.output_directory / "source_binding_receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Assertions must remain enabled.")
    main()
