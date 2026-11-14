#!/usr/bin/env python3
"""Check the finite resolved-graph facts used by combined_source_macros.tex.

This is not a Lean checker or a bounded approximation to a loop theorem.
It verifies the literal source rows to which the written induction applies.
All defaults are relative to this research checkout; arguments allow packaging.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def source_tree(path):
    nodes = {}
    token = re.compile(r"\(|\)|\.[A-Za-z]+|[A-Za-z][A-Za-z0-9]*|\d+")

    def parse(ts, i=0):
        t = ts[i]
        if t == "(":
            value, j = parse(ts, i + 1)
            require(ts[j] == ")", "missing closing parenthesis")
            return value, j + 1
        if t == ".node":
            left, j = parse(ts, i + 1)
            right, j = parse(ts, j)
            return (left, right), j
        if t == ".leaf":
            op, j = parse(ts, i + 1)
            return ("leaf", op), j
        if t in (".inc", ".dec", ".breakTo", ".continueTo"):
            return (t[1:], int(ts[i + 1])), i + 2
        if t == ".halt":
            return ("halt",), i + 1
        return nodes[t], i + 1

    for line in path.read_text().splitlines():
        m = re.fullmatch(r"def (\w+) : Tree := (.*)", line)
        if m:
            ts = token.findall(m[2])
            value, end = parse(ts)
            require(end == len(ts), "unparsed source tokens")
            nodes[m[1]] = value
    return nodes["trie"]


def flatten(tree, path=()):
    if tree[0] == "leaf":
        return [(path, tree[1])]
    return flatten(tree[0], path + (0,)) + flatten(tree[1], path + (1,))


def resolve(sites):
    def successor(path):
        for i in range(len(path) - 1, -1, -1):
            if path[i] == 0:
                return path[:i] + (1,) + (0,) * (len(path) - i - 1)
        return None

    def cut(path, value, count):
        for i in range(len(path) - 1, -1, -1):
            if path[i] == value:
                count -= 1
                if count == 0:
                    return path[:i]
        raise ValueError("invalid relative jump")

    def locate(path):
        if path is None:
            return 0
        for i, (other, _) in enumerate(sites):
            if (other[:len(path)] == path or
                (path[:len(other)] == other and not any(path[len(other):]))):
                return i
        raise ValueError("unresolved target")

    out = []
    for path, op in sites:
        if op[0] == "inc":
            out.append(("inc", op[1], locate(successor(path))))
        elif op[0] == "dec":
            out.append(("dec", op[1], locate(successor(cut(path, 0, 1))),
                        locate(successor(path))))
        elif op[0] == "breakTo":
            out.append(("jump", locate(successor(cut(path, 0, op[1])))))
        elif op[0] == "continueTo":
            out.append(("jump", locate(cut(path, 1, op[1]))))
        elif op[0] == "halt":
            out.append(("halt",))
        else:
            raise ValueError("unknown opcode")
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--old", type=Path, default=ROOT / "sources/BusyBeaver/PA196/Program.lean")
    parser.add_argument("--new", type=Path, default=ROOT / "work/helper_synthesis/h_only_mp_h_sites.json")
    parser.add_argument("--output", type=Path, default=HERE / "source_binding_receipt.json")
    args = parser.parse_args()
    old = resolve(flatten(source_tree(args.old)))
    new = resolve([(tuple(p), tuple(o)) for p, o in json.loads(args.new.read_text())])
    require(len(old) == 3812, "old site count")
    require(len(new) == 3788, "new site count")
    prefix_changes = {
        48: (("dec", 3, 3800, 49), ("dec", 3, 3777, 49)),
        3692: (("jump", 3799), ("jump", 3776)),
        3772: (("jump", 3799), ("jump", 3776)),
    }
    observed = {i: (old[i], new[i]) for i in range(3773) if old[i] != new[i]}
    require(observed == prefix_changes, "unexpected change in the reused prefix")
    expected_tail = [
        ("dec", 4, 3776, 3774), ("inc", 5, 3775), ("jump", 3773),
        ("jump", 25),
        ("dec", 1, 3779, 3778), ("jump", 3777),
        ("dec", 5, 3783, 3780), ("inc", 1, 3781),
        ("inc", 6, 3782), ("jump", 3779),
        ("dec", 6, 3786, 3784), ("inc", 5, 3785), ("jump", 3783),
        ("inc", 6, 3787), ("jump", 0),
    ]
    require(new[3773:] == expected_tail, "new tail differs from proved loop templates")
    require(new[:25] == old[:25], "root guard or stack decoder changed")
    require(new[25:48] == old[25:48], "scheduler arithmetic changed")
    require(new[49:3692] == old[49:3692], "AX body changed")
    require(new[3693:3772] == old[3693:3772], "MP prelude changed")
    receipt = {
        "status": "pass", "old_sites": len(old), "new_sites": len(new),
        "unchanged_prefix_rows": 3770,
        "relocated_prefix_rows": {str(i): value for i, value in observed.items()},
        "new_tail": {str(3773 + i): row for i, row in enumerate(expected_tail)},
        "sha256_old": hashlib.sha256(args.old.read_bytes()).hexdigest(),
        "sha256_new": hashlib.sha256(args.new.read_bytes()).hexdigest(),
        "scope": "Finite resolved instruction identities. Universal arithmetic loop proofs are written separately; no Lean claim.",
    }
    args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in ("new_tail", "relocated_prefix_rows")}, indent=2))


if __name__ == "__main__":
    main()
