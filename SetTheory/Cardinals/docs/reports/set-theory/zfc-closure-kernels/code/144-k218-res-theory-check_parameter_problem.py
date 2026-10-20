#!/usr/bin/env python3
"""Audit the exported finite search against its exact source checkpoint.

The C++20 enumerator performs the full exhaustive search. This independent
standard-library auditor reconstructs its input and checks the complete
histogram, template reachability, and both advertised minimizing choices.
"""
import argparse
from functools import cache
import hashlib
import itertools
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--data", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    sites = json.loads(args.source.read_text())
    by_pc = {pc: (op, arg) for pc, op, arg in sites}
    assert len(by_pc) == len(sites) == 4744
    prefixes = {pc[:i] for pc in by_pc for i in range(len(pc))}

    def parse(pc):
        if pc in by_pc:
            assert pc not in prefixes
            return by_pc[pc]
        assert pc in prefixes
        return parse(pc + "0"), parse(pc + "1")

    T = parse("")
    leaf = lambda t: isinstance(t[0], str)

    @cache
    def length(t):
        return 1 if leaf(t) else length(t[0]) + length(t[1])

    @cache
    def descendants(t):
        return frozenset([t]) if leaf(t) else frozenset([t]) | descendants(t[0]) | descendants(t[1])

    assert len(descendants(T)) == 205
    bounds = [135, 486, 895, 1178, 1474, 1773, 2069, 2419, 2650]
    perms = list(itertools.permutations((4, 5, 3)))
    nodes, intern, templates, ti = [], {}, [], {}

    def node(t):
        if t not in intern:
            intern[t] = len(nodes)
            nodes.append(t)
        return intern[t]

    @cache
    def encode(t):
        return node(t) if leaf(t) else node((encode(t[0]), encode(t[1])))

    @cache
    def rename(t, p):
        if leaf(t):
            op, reg = t
            if op in ("CI", "CD") and reg in (3, 4, 5):
                reg = perms[p][(4, 5, 3).index(reg)]
            return op, reg
        return rename(t[0], p), rename(t[1], p)

    def template(t):
        if t not in ti:
            ti[t] = len(templates)
            templates.append(t)
        return ti[t]

    def build(t, lo=0):
        hi = lo + length(t)
        for row in range(8):
            if bounds[row] <= lo and hi <= bounds[row + 1]:
                choices = tuple(encode(rename(t, p)) for p in range(6))
                return template(("fixed", choices[0])) if len(set(choices)) == 1 else template(("slot", row, *choices))
        if hi <= bounds[0] or lo >= bounds[-1]:
            return template(("fixed", encode(t)))
        assert not leaf(t)
        return template(("pair", build(t[0], lo), build(t[1], lo + length(t[0]))))

    root = build(T)
    baseline = encode(T)
    exported = {"nodes": nodes, "template": templates, "root_template": root,
                "baseline_root": baseline, "bounds": bounds, "permutations": perms}
    assert json.loads(json.dumps(exported)) == json.loads((args.data / "parameter_problem.json").read_text())
    integer = [f"{len(nodes)} {len(templates)} {root}"]
    integer.extend("-1 -1" if isinstance(a, str) else f"{a} {b}" for a, b in nodes)
    for t in templates:
        if t[0] == "fixed":
            integer.append(f"0 {t[1]}")
        elif t[0] == "slot":
            integer.append("1 " + " ".join(map(str, t[1:])))
        else:
            integer.append(f"2 {t[1]} {t[2]}")
    assert "\n".join(integer) + "\n" == (args.data / "parameter_problem.in").read_text()
    reachable = set()

    def visit(i):
        if i in reachable:
            return
        reachable.add(i)
        if templates[i][0] == "pair":
            visit(templates[i][1])
            visit(templates[i][2])

    visit(root)
    assert len(reachable) == len(templates) == 97
    hist = {}
    for line in (args.data / "parameter_exhaustive.log").read_text().splitlines():
        words = line.split()
        if len(words) == 2 and all(w.isdigit() for w in words):
            hist[int(words[0])] = int(words[1])
    assert sum(hist.values()) == 6 ** 8
    assert min(hist) == 205 and hist[205] == 2
    minima = []
    for line in (args.data / "parameter_best.txt").read_text().splitlines():
        count, *choice = map(int, line.split())
        assert count == 205 and len(choice) == 8 and all(0 <= v < 6 for v in choice)

        # Directly rename individual source leaves, without using the template.
        def instantiate(t, lo=0):
            if leaf(t):
                for row in range(8):
                    if bounds[row] <= lo < bounds[row + 1]:
                        return rename(t, choice[row])
                return t
            return instantiate(t[0], lo), instantiate(t[1], lo + length(t[0]))

        assert len(descendants(instantiate(T))) == count
        minima.append(choice)
    assert len(minima) == 2 and len(set(map(tuple, minima))) == 2
    print(json.dumps({"status": "PARAMETER_PROBLEM_AUDIT_PASS",
                      "scope": "Fixed tree shape; eight independent six-way row register permutations",
                      "source_sha256": hashlib.sha256(args.source.read_bytes()).hexdigest(),
                      "integer_problem_sha256": hashlib.sha256((args.data / "parameter_problem.in").read_bytes()).hexdigest(),
                      "source_nodes": 205, "initial_pool_nodes": len(nodes),
                      "templates": len(templates), "reachable_templates": len(reachable),
                      "choices": sum(hist.values()), "minimum": min(hist),
                      "minimizing_choices": minima, "histogram": hist}, indent=2))


if __name__ == "__main__":
    main()
