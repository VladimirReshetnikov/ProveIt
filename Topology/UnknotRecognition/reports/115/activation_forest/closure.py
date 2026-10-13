"""Exact exceptional-boundary Horn closure, with nonunit prerequisites retained."""
from __future__ import annotations
from .model import Instance


def bits(mask: int):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class Activation:
    def __init__(self, inst: Instance):
        m = inst.m
        adj = [0] * m
        anchors = 0
        high = []
        boundary = set()
        for h in range(inst.columns):
            supp = [e for e in range(m) if inst.matrix[e][h] != 0]
            units = [e for e in supp if inst.matrix[e][h] == 1]
            if not units:
                continue
            if len(supp) == 1:
                anchors |= 1 << supp[0]
            elif len(supp) == 2:
                for target in units:
                    source = supp[0] if supp[1] == target else supp[1]
                    adj[source] |= 1 << target
            else:
                high.append((supp, units))
                boundary.update(supp)
        reach = [adj[e] | (1 << e) for e in range(m)]
        for k in range(m):
            for e in range(m):
                if reach[e] >> k & 1:
                    reach[e] |= reach[k]
        # SCCs from exact transitive closure: deliberately simple polynomial code.
        rest = set(range(m))
        sccs = []
        while rest:
            e = min(rest)
            component = {x for x in rest if (reach[e] >> x & 1) and (reach[x] >> e & 1)}
            sccs.append(component)
            rest -= component
        mandatory = []
        for part in sccs:
            mask = sum(1 << e for e in part)
            is_source = not any(adj[e] & mask for e in range(m) if e not in part)
            if is_source and not (mask & anchors) and not (part & boundary):
                mandatory.append(part)
        self.boundary = sorted(boundary)
        self.b = len(boundary)
        self.full = (1 << self.b) - 1
        self.mandatory = mandatory
        self.reach = reach
        self.anchors = anchors
        self.adj = adj
        self.sccs = sccs
        self.masks = [sum(1 << i for i, x in enumerate(self.boundary) if reach[e] >> x & 1)
                      for e in range(m)]
        initial = anchors | sum(1 << e for part in mandatory for e in part)
        reached = initial
        for e in bits(initial):
            reached |= reach[e]
        self.base = sum(1 << i for i, e in enumerate(self.boundary) if reached >> e & 1)
        index = {e: i for i, e in enumerate(self.boundary)}
        self.rules = []
        for supp, units in high:
            mask = sum(1 << index[e] for e in supp)
            for e in units:
                target = 1 << index[e]
                self.rules.append((mask ^ target, target))
        self.cache: dict[int, int] = {}

    def close(self, mask: int) -> int:
        if mask < 0 or mask & ~self.full:
            raise ValueError('mask outside exceptional boundary')
        if mask in self.cache:
            return self.cache[mask]
        start = mask
        mask |= self.base
        while True:
            old = mask
            for i in bits(mask):
                mask |= self.masks[self.boundary[i]]
            for premise, target in self.rules:
                if premise & mask == premise:
                    mask |= target
            if mask == old:
                self.cache[start] = mask
                return mask

    def seed_closure(self, edges) -> int:
        mask = 0
        for e in edges:
            mask |= self.masks[e]
        return self.close(mask)
