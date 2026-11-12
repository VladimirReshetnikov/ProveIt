"""Untrusted certificate translator: Choice-DI to uniform continuations.

The translator is deliberately outside every measured proof checker.  It
first reconstructs a successful old checking trace, then serializes it with
the new administrative allocations and the new context's hypothesis pruning.
It does not establish the universal soundness or bi-interpretation theorem.
"""
from __future__ import annotations

import argparse
import ast
import copy
import json
import math
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class Node:
    kind: str
    goal: object
    packet: object = None
    children: list["Node"] = field(default_factory=list)
    allocated: int | None = None


class Trace:
    """Readable reconstruction of the retained baseline byte checker."""

    def __init__(self, packet):
        self.data = copy.deepcopy(packet)
        self.goal = self.data.pop()
        self.k = 0

    def opening(self, a, t=None, d=0):
        if type(a) is list:
            return [self.opening(b, t, d + b" \2\1\4"[len(a)]) for b in a]
        return a if self.k <= a < d else d % 2 and self.opening(t, d=1)

    def check(self, a, g):
        if self.opening(a) in g:
            return Node("hyp", a)
        packet = self.data.pop()
        m, t = packet
        node = Node("", a, packet)
        if m:
            node.children.append(self.check(m, g))
            h = m[2:]
            if not h:
                node.kind = "specialize"
                s, u, t = m + [t] if m[1:] else [0, t] + m
                if self.opening(t, u) != a:
                    raise ValueError("The old specialization target fails")
                node.children.append(self.check(self.opening(t, s), g))
                return node
            node.kind = "eliminate"
        elif t:
            node.kind = "introduce"
            h = a = self.opening(a[2], t, 2)
        else:
            node.kind = "compute"
            (n, t, r), b = a
            if n:
                n, = n
                t = self.opening(r, [n, t, r], 1)
            if b != t:
                raise ValueError("The old computation fails")
            return node
        self.k -= 1
        node.allocated = self.k
        image = self.k if m or len(a) % 2 == m else 0
        node.children.append(self.check(self.opening(a, [self.k]),
                                        g + [self.opening(h, image)]))
        return node

    def run(self):
        return self.check(self.goal, [])


class Compiler:
    def __init__(self):
        self.k = 0
        self.names = {}
        self.consumed = []
        self.administrative_allocations = 0
        self.pruned_nodes = 0

    def opening(self, a, t=None, d=0):
        if type(a) is list:
            return [self.opening(b, t, d + b" \2\1\4"[len(a)]) for b in a]
        return a if self.k <= a < d else d % 2 and self.opening(t, d=1)

    def rename(self, value):
        if type(value) is list:
            return [self.rename(x) for x in value]
        if type(value) in (int, float) and math.isfinite(value) and value < 0:
            old = math.floor(value)
            if old in self.names:
                return self.names[old] + value - old
        return value

    def forget(self, node):
        """Instantiate private names of a pruned subproof by zero.

        They cannot occur in its retained conclusion or context.  Later
        certificates may nevertheless mention an old globally allocated name
        as an arbitrary numerical parameter, for which zero is a valid image.
        """
        self.pruned_nodes += 1
        if node.allocated is not None:
            self.names[node.allocated] = 0
        for child in node.children:
            self.forget(child)

    def compile(self, node, a, g):
        if self.opening(a) in g:
            self.forget(node)
            return
        if node.kind == "hyp":
            raise ValueError("An inherited hypothesis did not translate")
        old_m, old_t = node.packet
        # Reserve this packet now.  Its payload can refer to names allocated
        # inside the major proof, so finish renaming it after that proof.
        packet = [self.rename(old_m), None]
        self.consumed.append(packet)
        if old_m:
            self.compile(node.children[0], packet[0], g)
        packet[1] = self.rename(old_t)
        m, t = packet
        if node.kind == "compute":
            (n, initial, r), b = a
            if n:
                n, = n
                initial = self.opening(r, [n, initial, r], 1)
            if b != initial:
                raise ValueError("A translated computation does not match")
            return
        if node.kind == "specialize":
            s, u, t = m + [t] if m[1:] else [0, t] + m
            if self.opening(t, u) != a:
                raise ValueError("A translated specialization does not match")
            a = self.opening(t, s)
            h = []
            self.administrative_allocations += 1
        elif node.kind == "eliminate":
            h = m[2:]
        elif node.kind == "introduce":
            h = a = self.opening(a[2], t, 2)
        else:
            raise ValueError("Unknown checking-trace node")
        self.k -= 1
        if node.allocated is not None:
            self.names[node.allocated] = self.k
        image = self.k if m or len(a) % 2 == m else 0
        self.compile(node.children[-1], self.opening(a, [self.k]),
                     g + [self.opening(h, image)])


def translate(packet):
    trace = Trace(packet)
    tree = trace.run()
    compiler = Compiler()
    compiler.compile(tree, trace.goal, [])
    translated = list(reversed(compiler.consumed)) + [trace.goal]
    stats = {
        "old_allocations": -trace.k,
        "new_allocations": -compiler.k,
        "administrative_allocations": compiler.administrative_allocations,
        "pruned_trace_nodes": compiler.pruned_nodes,
        "unused_original_prefix_cells": len(trace.data),
        "old_packet_cells": len(packet),
        "new_packet_cells": len(translated),
    }
    return translated, stats


def kernel_core(path):
    tree = ast.parse(Path(path).read_text())
    tree.body = [n for n in tree.body if isinstance(
        n, (ast.Import, ast.ImportFrom, ast.FunctionDef, ast.Assign))]
    return compile(ast.fix_missing_locations(tree), str(path), "exec")


def accepts_uniform(core, packet):
    namespace = {}
    exec(core, namespace)
    data = copy.deepcopy(packet)
    try:
        namespace["q"] = data.pop
        namespace["c"](data.pop(), [])
        return True
    except BaseException:
        return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cases", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--kernel", type=Path, action="append", default=[])
    args = parser.parse_args()
    cases = json.loads(args.cases.read_text())["cases"]
    cores = [(str(p), kernel_core(p)) for p in args.kernel]
    output, failures = [], []
    for case in cases:
        if not case["accept"]:
            continue
        try:
            packet, stats = translate(case["packet"])
            checks = {p: accepts_uniform(core, packet) for p, core in cores}
            if not all(checks.values()):
                raise ValueError("A uniform kernel rejects: " + repr(checks))
            output.append({"name": case["name"], "packet": packet,
                           "accept": True, "translation": stats})
        except BaseException as error:
            failures.append({"name": case["name"], "error": repr(error)})
    result = {"source": str(args.cases), "cases": output,
              "translation_failures": failures,
              "scope": "Successful old certificates only; kernels and metatheorems remain separate."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"translated": len(output), "failures": failures,
                      "output": str(args.output)}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
