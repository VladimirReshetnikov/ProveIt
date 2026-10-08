"""Small-sheet oracle: literal permutations and exhaustive vertex gauges.

No compressed-cover module, gcd, CRT, spanning forest, or coset arithmetic is
used by the oracle. This file is for finite validation, not large inputs.
"""

from copy import deepcopy
from itertools import product


def element(parity=0, shift=0):
    return {"parity": parity, "shift": shift}


def make_assembly(kind, modulus, vertices, graph_edges, phases=None, extras=()):
    """Connected local covers; graph ports have trivial peripheral monodromy."""
    degrees = [0] * vertices
    for u, v in graph_edges:
        degrees[u] += 1
        degrees[v] += 1
    blocks = []
    for degree in degrees:
        maps = [element() for _ in range(degree)]
        maps.extend(element(0, shift) for shift in extras)
        maps.append(element(0, 1))
        if kind == "dihedral":
            maps.append(element(1, 0))
        blocks.append({"surface": {"orientable": True, "genus": 0,
                                   "boundary_components": len(maps) + 1},
                       "monodromy": maps})
    used = [0] * vertices
    edges = []
    for i, (u, v) in enumerate(graph_edges):
        source = {"block": u, "boundary": used[u]}
        used[u] += 1
        target = {"block": v, "boundary": used[v]}
        used[v] += 1
        phase = element() if phases is None else deepcopy(phases[i])
        edges.append({"source": source, "target": target, "phase": phase})
    return {"group": {"kind": kind, "modulus": modulus}, "blocks": blocks, "edges": edges}


def compose(left, right):
    return tuple(left[right[i]] for i in range(len(left)))


def inverse(permutation):
    result = [0] * len(permutation)
    for i, j in enumerate(permutation):
        result[j] = i
    return tuple(result)


class ExpandedGroup:
    def __init__(self, kind, modulus):
        self.kind, self.modulus = kind, modulus
        self.size = modulus * (2 if kind == "dihedral" else 1)
        identity = tuple(range(self.size))
        translation = tuple((x // modulus) * modulus + (x + 1) % modulus
                            for x in range(self.size))
        reflection = tuple((1 - x // modulus) * modulus + (-x) % modulus
                           for x in range(self.size)) if kind == "dihedral" else identity
        powers = [identity]
        for _ in range(1, modulus):
            powers.append(compose(translation, powers[-1]))
        self.left = list(powers)
        if kind == "dihedral":
            self.left.extend(compose(p, reflection) for p in powers)
        lookup = {permutation: i for i, permutation in enumerate(self.left)}
        self.table = [[lookup[compose(p, q)] for q in self.left] for p in self.left]
        self.inverses = [lookup[inverse(p)] for p in self.left]
        self.right = [tuple(self.table[x][h] for x in range(self.size))
                      for h in range(self.size)]

    def encode(self, value):
        return value["parity"] * self.modulus + value["shift"] % self.modulus

    def decode(self, value):
        return element(value // self.modulus, value % self.modulus)

    def peripheral(self, block):
        maps = [self.left[self.encode(x)] for x in block["monodromy"]]
        genus = block["surface"]["genus"]
        sequence = []
        for i in range(genus):
            a, b = maps[2 * i:2 * i + 2]
            sequence.extend((a, b, inverse(a), inverse(b)))
        boundaries = list(maps[2 * genus:])
        sequence.extend(boundaries)
        relation = tuple(range(self.size))
        for permutation in sequence:
            relation = compose(permutation, relation)
        boundaries.append(inverse(relation))
        return boundaries

    def orbit(self, permutation, point):
        result = set()
        while point not in result:
            result.add(point)
            point = permutation[point]
        return result

    def all_gauges(self, source, target, marks=()):
        peripheral = [self.peripheral(block) for block in source["blocks"]]
        accepted = set()
        for gauges in product(range(self.size), repeat=len(source["blocks"])):
            valid = True
            for edge, other in zip(source["edges"], target["edges"]):
                u, v = edge["source"]["block"], edge["target"]["block"]
                a, b = self.encode(edge["phase"]), self.encode(other["phase"])
                lhs = compose(self.right[gauges[v]], self.right[a])
                rhs = compose(self.right[b], self.right[gauges[u]])
                if lhs != rhs:
                    valid = False
                    break
            if not valid:
                continue
            for mark in marks:
                v = mark["block"]
                image = self.right[gauges[v]][self.encode(mark["source"])]
                target_point = self.encode(mark["target"])
                if mark["kind"] == "point":
                    valid = image == target_point
                else:
                    cycle = self.orbit(peripheral[v][mark["boundary"]], target_point)
                    valid = image in cycle
                if not valid:
                    break
            if valid:
                accepted.add(gauges)
        return accepted

    def change_gauges(self, source, gauges):
        target = deepcopy(source)
        for edge in target["edges"]:
            u, v = edge["source"]["block"], edge["target"]["block"]
            old = self.encode(edge["phase"])
            new = self.table[self.inverses[gauges[u]]][self.table[old][gauges[v]]]
            edge["phase"] = self.decode(new)
        return target


def brute_phase_orbits(kind, modulus, vertices, graph_edges):
    """Number of orbits of ALL edge phases under ALL vertex gauges."""
    group = ExpandedGroup(kind, modulus)
    remaining = set(product(range(group.size), repeat=len(graph_edges)))
    count = 0
    while remaining:
        phases = next(iter(remaining))
        orbit = set()
        for gauges in product(range(group.size), repeat=vertices):
            moved = []
            for phase, (u, v) in zip(phases, graph_edges):
                moved.append(group.table[group.inverses[gauges[u]]][
                    group.table[phase][gauges[v]]])
            orbit.add(tuple(moved))
        remaining.difference_update(orbit)
        count += 1
    return count
