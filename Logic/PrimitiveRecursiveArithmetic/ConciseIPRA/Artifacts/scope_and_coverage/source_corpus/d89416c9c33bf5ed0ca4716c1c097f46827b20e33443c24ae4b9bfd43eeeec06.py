"""Untrusted proof translation to endpoint certificates with uniform tails.

Adapted from ProveIt's named-specialization translate_uniform.py.  This
module is not imported by any measured checker.  It reconstructs the old
proof tree and then allocates new labels, because administrative tails
add fresh parameters.  It supports ordinary and elimination-only context
use; the latter is the separate Eq/D object-language presentation.
"""
from __future__ import annotations

import copy
import math
from dataclasses import dataclass, field


@dataclass
class Node:
    kind: str
    goal: object
    packet: object = None
    children: list["Node"] = field(default_factory=list)
    allocated: int | None = None


class Trace:
    def __init__(self, packet, focused=False):
        self.data = copy.deepcopy(packet)
        self.k = 0
        self.focused = focused
        self.goal = self.data.pop()
        if focused:
            self.goal = self.opening(self.goal)

    def opening(self, a, t=None, d=0):
        if type(a) is list:
            return [self.opening(b, t, d + b" \2\1\4"[len(a)]) for b in a]
        return a if self.k <= a < d else d % 2 and self.opening(t, d=1)

    def check(self, a, g, major=False):
        if (not self.focused or major) and self.opening(a) in g:
            return Node("hyp", a)
        packet = self.data.pop()
        m, t = packet
        node = Node("", a, packet)
        if m:
            node.children.append(self.check(m, g, major=True))
            h = m[2:]
            if not h:
                node.kind = "specialize"
                s, u, t = m + [t] if m[1:] else [0, t] + m
                if self.opening(t, u) != a:
                    raise ValueError("Old specialization target mismatch")
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
                raise ValueError("Old computation mismatch")
            return node
        self.k -= 1
        node.allocated = self.k
        image = self.k if m or len(a) % 2 == m else 0
        node.children.append(self.check(self.opening(a, [self.k]),
                                        g + [self.opening(h, image)]))
        return node


class Compiler:
    def __init__(self, focused=False):
        self.k = 0
        self.focused = focused
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
        self.pruned_nodes += 1
        if node.allocated is not None:
            self.names[node.allocated] = 0
        for child in node.children:
            self.forget(child)

    def compile(self, node, a, g, major=False):
        if (not self.focused or major) and self.opening(a) in g:
            self.forget(node)
            return
        if node.kind == "hyp":
            raise ValueError("A retained assumption failed to translate")
        old_m, old_t = node.packet
        packet = [self.rename(old_m), None, None, None]
        self.consumed.append(packet)
        if old_m:
            self.compile(node.children[0], packet[0], g, major=True)
        m, payload = packet[0], self.rename(old_t)
        if m and len(m) <= 2:
            s, u, t = m + [payload] if m[1:] else [0, payload] + m
            packet[1:] = [s, u, t]
        else:
            packet[1:] = [0, 0, payload]
        if node.kind == "compute":
            (n, initial, r), b = a
            if n:
                n, = n
                initial = self.opening(r, [n, initial, r], 1)
            if b != initial:
                raise ValueError("Translated computation mismatch")
            return
        if node.kind == "specialize":
            _, s, u, t = packet
            if self.opening(t, u) != a:
                raise ValueError("Translated specialization mismatch")
            a = self.opening(t, s)
            h = []
            self.administrative_allocations += 1
        elif node.kind == "eliminate":
            h = m[2:]
        elif node.kind == "introduce":
            h = a = self.opening(a[2], payload, 2)
        else:
            raise ValueError("Unknown checking-trace node")
        self.k -= 1
        if node.allocated is not None:
            self.names[node.allocated] = self.k
        image = self.k if m or len(a) % 2 == m else 0
        self.compile(node.children[-1], self.opening(a, [self.k]),
                     g + [self.opening(h, image)])


def translate(packet, focused=False):
    trace = Trace(packet, focused)
    tree = trace.check(trace.goal, [])
    compiler = Compiler(focused)
    compiler.compile(tree, trace.goal, [])
    output = list(reversed(compiler.consumed)) + [trace.goal]
    return output, {
        "old_allocations": -trace.k,
        "new_allocations": -compiler.k,
        "administrative_allocations": compiler.administrative_allocations,
        "pruned_nodes": compiler.pruned_nodes,
        "unused_original_prefix_cells": len(trace.data),
        "old_packet_cells": len(packet),
        "new_packet_cells": len(output),
        "focused": focused,
    }


def endpoints_only(packet):
    """Reformat already-uniform two-field data; do not rename any labels."""
    data = copy.deepcopy(packet)
    if not isinstance(data, list) or not data:
        return data
    for pos, item in enumerate(data[:-1]):
        if not isinstance(item, list) or len(item) != 2:
            continue
        m, t = item
        if m and isinstance(m, list) and len(m) == 2:
            data[pos] = [m, m[0], m[1], t]
        elif m and isinstance(m, list) and len(m) == 1:
            data[pos] = [m, 0, t, m[0]]
        else:
            data[pos] = [m, 0, 0, t]
    return data
