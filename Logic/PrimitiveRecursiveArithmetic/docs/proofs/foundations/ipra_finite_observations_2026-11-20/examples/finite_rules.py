"""Finite Horn closure, positive/negative certificates, and exact block refinement.

Body and state masks use one integer bit per ground atom. Rule order resolves ties.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Rule:
    head: int
    body: int


@dataclass(frozen=True)
class Entry:
    rule: int
    rank: int


class Presentation:
    def __init__(self, size, rules):
        if size < 0:
            raise ValueError("negative atom count")
        self.size = size
        self.rules = tuple(rules)
        self.full = (1 << size) - 1
        for rule in self.rules:
            if not (0 <= rule.head < size and 0 <= rule.body <= self.full):
                raise ValueError("invalid rule")

    def step(self, state):
        result = state
        for rule in self.rules:
            if rule.body & state == rule.body:
                result |= 1 << rule.head
        return result

    def saturate(self):
        births = {}
        state = 0
        for rank in range(1, self.size + 1):
            after = state
            for i, rule in enumerate(self.rules):
                bit = 1 << rule.head
                if not after & bit and rule.body & state == rule.body:
                    births[rule.head] = Entry(i, rank)
                    after |= bit
            if after == state:
                break
            state = after
        return state, births

    def evidence(self, atom):
        if not 0 <= atom < self.size:
            raise ValueError("invalid request")
        state, births = self.saturate()
        if atom not in births:
            return "cut", state
        at = (births[atom].rank, atom)
        order = sorted(births, key=lambda a: (births[a].rank, a))
        return "proof", [births[a].rule for a in order if (births[a].rank, a) <= at]

    def verify(self, atom, evidence):
        if not 0 <= atom < self.size:
            return False
        kind, data = evidence
        if kind == "cut":
            return (isinstance(data, int) and 0 <= data <= self.full
                    and not (data >> atom & 1) and self.step(data) == data)
        if kind != "proof" or not isinstance(data, list) or not 0 < len(data) <= self.size:
            return False
        state = 0
        for i in data:
            if not isinstance(i, int) or not 0 <= i < len(self.rules):
                return False
            rule = self.rules[i]
            if state >> rule.head & 1 or rule.body & state != rule.body:
                return False
            state |= 1 << rule.head
        return rule.head == atom

    def signatures(self, colours):
        families = [{frozenset([colours[a]])} for a in range(self.size)]
        for rule in self.rules:
            body = frozenset(colours[b] for b in range(self.size) if rule.body >> b & 1)
            families[rule.head].add(body)
        return tuple(frozenset(d for d in f if not any(e < d for e in f)) for f in families)

    def refinement(self, colours):
        colours = canonical(colours)
        if len(colours) != self.size:
            raise ValueError("one initial colour required per atom")
        for _ in range(self.size):
            sig = self.signatures(colours)
            finer = canonical(zip(colours, sig))
            if colours == finer:
                break
            colours = finer
        return colours

    def quotient(self, colours):
        colours = canonical(colours)
        if len(colours) != self.size:
            raise ValueError("one colour required per atom")
        sig = self.signatures(colours)
        rules = []
        for c in range(max(colours, default=-1) + 1):
            members = [i for i, d in enumerate(colours) if c == d]
            family = sig[members[0]]
            if any(sig[i] != family for i in members):
                raise ValueError("unstable partition")
            for d in sorted(sum(1 << b for b in body) for body in family):
                rules.append(Rule(c, d))
        return Presentation(max(colours, default=-1) + 1, rules)


def canonical(values):
    """Number blocks by the order of their least atom."""
    names = {}
    return tuple(names.setdefault(x, len(names)) for x in values)


def lift(colours, state):
    return sum(1 << i for i, c in enumerate(colours) if state >> c & 1)


def sheet_example(close):
    roots = [(1, 0), (1, 1), (0, 1), (1, -1)]
    edges = [(0, 1), (1, 2), (2, 3)]
    if close:
        edges.append((3, 0))
    rules = [Rule(0, 0)]
    signs = []
    for u, v in edges:
        dot = sum(x * y for x, y in zip(roots[u], roots[v]))
        if dot == 0:
            raise ValueError("edge crosses the branch point")
        flip = int(dot < 0)
        signs.append(1 - 2 * flip)
        for s in range(2):
            a, b = 2 * u + s, 2 * v + (s ^ flip)
            rules.extend([Rule(b, 1 << a), Rule(a, 1 << b)])
    sys = Presentation(2 * len(roots), rules)
    return signs, sys


if __name__ == "__main__":
    for close in [False, True]:
        signs, sys = sheet_example(close)
        ev = sys.evidence(1)
        assert sys.verify(1, ev)
        print("closed" if close else "open", "edge signs", signs, "opposite initial sheet", ev)
    join = Presentation(6, [Rule(0, 0), Rule(3, 0), Rule(4, 5), Rule(5, 10)])
    print("join initial (0,0,1,1,2,2), stable", join.refinement([0, 0, 1, 1, 2, 2]))
