#!/usr/bin/env python3
"""Prove every supplied original Wade macro equivalent to its fine expansion.

Both programs are closed blocks followed by a distinguished return halt.  The
finite product relates matching decrement tests with equal nine-register
values.  Between tests, only increments and structural transfers occur;
equality of the nine increment multiplicities is an exact transformer proof.
The separately loaded upstream path interpreter rechecks every product edge.
This is an ordinary executable proof certificate, not a new kernel theorem.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import cache
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_dag(path):
    nodes = {}
    for match in re.finditer(r"\|\s+(\d+)\s+=>\s+\((E\w+(?:\s+\d+)?),\s*(E\w+(?:\s+\d+)?)\)", path.read_text()):
        key = int(match[1])
        assert key not in nodes
        nodes[key] = tuple(part.split() for part in match.groups()[1:])
    assert nodes and set(nodes) == set(range(len(nodes)))
    operators = {"EInc": "inc", "EDecnz": "dec", "EBreak": "brk", "EContinue": "cont"}
    active = set()

    @cache
    def expand(index):
        assert index not in active, "The declared finite macro DAG is cyclic."
        active.add(index)
        children = []
        for edge in nodes[index]:
            if edge == ["EHalt"]:
                children.append(("L", ("halt",)))
                continue
            op, arg = edge
            arg = int(arg)
            if op == "ENode":
                children.append(expand(arg))
            else:
                assert op in operators and arg >= 0
                if op in ("EInc", "EDecnz"):
                    assert arg < 9
                children.append(("L", (operators[op], arg)))
        active.remove(index)
        return ("N", *children)

    return expand, len(nodes)


@cache
def bounds(tree):
    if tree[0] == "L":
        op, *arg = tree[1]
        if op == "dec":
            return 1, 0
        if op == "brk":
            return arg[0], 0
        if op == "cont":
            return 0, arg[0]
        return 0, 0
    left, right = bounds(tree[1]), bounds(tree[2])
    return max(left[0] - 1, right[0], 0), max(left[1], right[1] - 1, 0)


def fine_vocabulary(path):
    data = json.loads(path.read_text())
    ast = data["ast_dag"]

    @cache
    def original(index):
        row = ast[index]
        if row[0] == "L":
            assert row[1][0] in ("inc", "dec", "brk", "cont", "halt")
            return "L", tuple(row[1])
        assert row[0] == "N"
        return "N", original(row[1]), original(row[2])

    @cache
    def finest(index):
        row = ast[index]
        if row[0] == "N" and bounds(original(row[1])) == bounds(original(row[2])) == (0, 0):
            return finest(row[1]) + finest(row[2])
        return (index,)

    assert len(data["atoms"]) == 44
    roots = [atom["ast"] for atom in data["atoms"].values()]
    assert all(bounds(original(i)) == (0, 0) for i in roots)
    indices = sorted({i for root in roots for i in finest(root)})
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
    assert len(indices) <= len(alphabet)
    encoding = dict(zip(alphabet, indices))
    return {c: original(i) for c, i in encoding.items()}, encoding


def sequence(trees):
    assert trees
    if len(trees) == 1:
        return trees[0]
    split = len(trees) // 2
    return "N", sequence(trees[:split]), sequence(trees[split:])


def leaves(tree, prefix=""):
    if tree[0] == "L":
        return {prefix: tree[1]}
    return leaves(tree[1], prefix + "0") | leaves(tree[2], prefix + "1")


def increment(word):
    # Ordinary finite-width binary increment, including the empty width.
    width = len(word)
    value = (int(word, 2) if word else 0) + 1
    return format(value % (1 << width), f"0{width}b") if width else ""


def strip(word, bit, count):
    positions = [index for index, value in enumerate(word) if value == bit]
    return word if count == 0 else word[:positions[-count]] if len(positions) >= count else ""


class Graph:
    def __init__(self, block):
        assert bounds(block) == (0, 0)
        assert all(edge[0] != "halt" for edge in leaves(block).values())
        self.tree = ("N", block, ("L", ("halt",)))
        self.leaves = leaves(self.tree)
        self.maximum = max(map(len, self.leaves))
        assert self.leaves["1"] == ("halt",)

    def decode(self, word):
        for length in range(1, self.maximum + 1):
            pc = (word + "0" * self.maximum)[:length]
            if pc in self.leaves:
                return pc
        raise AssertionError("The wrapped source tree must be complete.")

    def next_word(self, pc, positive=None):
        op, *arg = self.leaves[pc]
        if op == "inc" or (op == "dec" and positive):
            return increment(pc)
        if op == "dec":
            return increment(strip(pc, "0", 1))
        if op == "brk":
            return increment(strip(pc, "0", arg[0]))
        if op == "cont":
            return strip(pc, "1", arg[0])
        raise AssertionError("A return is not an ordinary transfer.")

    def segment(self, word):
        pc = self.decode(word)
        seen = set()
        trace = []
        additions = [0] * 9
        while self.leaves[pc][0] not in ("dec", "halt"):
            assert pc not in seen, "An unconditional infinite loop cannot be a finite segment."
            seen.add(pc)
            edge = self.leaves[pc]
            trace.append(pc)
            if edge[0] == "inc":
                additions[edge[1]] += 1
            pc = self.decode(self.next_word(pc))
        return pc, additions, trace


def make_certificate(left, right):
    a, ai, at = left.segment("")
    b, bi, bt = right.segment("")
    assert ai == bi, ("Initial increment vector", ai, bi)
    vertices = []
    index = {}
    queue = deque()

    def intern(a, b):
        if (a, b) not in index:
            index[a, b] = len(vertices)
            vertices.append({"left_pc": a, "right_pc": b})
            queue.append(index[a, b])
        return index[a, b]

    initial = intern(a, b)
    while queue:
        i = queue.popleft()
        vertex = vertices[i]
        a, b = vertex["left_pc"], vertex["right_pc"]
        ea, eb = left.leaves[a], right.leaves[b]
        assert ea == eb, (i, a, b, ea, eb)
        vertex["operation"] = list(ea)
        if ea == ("halt",):
            assert a == b == "1"
            continue
        assert ea[0] == "dec"
        for positive, name in ((True, "positive"), (False, "zero")):
            pa, ia, ta = left.segment(left.next_word(a, positive))
            pb, ib, tb = right.segment(right.next_word(b, positive))
            assert ia == ib, (i, name, ia, ib)
            vertex[name] = dict(target=intern(pa, pb), increments=ia, left_segment=ta, right_segment=tb)
    return dict(initial_pair=initial, initial_increments=ai, initial_left_segment=at,
                initial_right_segment=bt, vertices=vertices)


def check_with_upstream(left, right, certificate, paths):
    """Recheck generated graph with the separately attributed path evaluator."""
    def bits(word):
        return [char == "1" for char in word]

    def upstream_segment(graph, word):
        additions, endpoint = paths.seg(graph.tree, bits(word))
        edge, actual = paths.site(graph.tree, endpoint)
        pc = "".join("1" if value else "0" for value in actual)
        assert graph.leaves[pc] == edge
        return pc, [additions.count(r) for r in range(9)]

    vertices = certificate["vertices"]
    first = vertices[certificate["initial_pair"]]
    for graph, key in ((left, "left_pc"), (right, "right_pc")):
        pc, additions = upstream_segment(graph, "")
        assert pc == first[key] and additions == certificate["initial_increments"]
    seen = {certificate["initial_pair"]}
    queue = deque(seen)
    while queue:
        index = queue.popleft()
        vertex = vertices[index]
        for graph, key in ((left, "left_pc"), (right, "right_pc")):
            operation, raw = paths.site(graph.tree, bits(vertex[key]))
            assert list(operation) == vertex["operation"]
            assert "".join("1" if b else "0" for b in raw) == vertex[key]
        if vertex["operation"] == ["halt"]:
            assert vertex["left_pc"] == vertex["right_pc"] == "1"
            assert "positive" not in vertex and "zero" not in vertex
            continue
        assert vertex["operation"][0] == "dec"
        for name, operation in (("positive", paths.inc_path), ("zero", lambda p: paths.brk(1, p))):
            branch = vertex[name]
            target = branch["target"]
            assert type(target) is int and 0 <= target < len(vertices)
            for graph, key in ((left, "left_pc"), (right, "right_pc")):
                successor = operation(bits(vertex[key]))
                word = "".join("1" if b else "0" for b in successor)
                pc, additions = upstream_segment(graph, word)
                assert pc == vertices[target][key] and additions == branch["increments"]
            if target not in seen:
                seen.add(target)
                queue.append(target)
    assert seen == set(range(len(vertices)))

