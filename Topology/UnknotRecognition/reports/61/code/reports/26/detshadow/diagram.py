"""Planar-diagram shadows, exact at q=1 and q=i, plus an exponential oracle.

Crossing slots are cyclic, opposite slots are strands, and smoothing zero is
(0,1)(2,3). Empty PD data require an explicit positive free-circle count.
All integers are exact. No external knot tables or numeric determinants.
"""
from __future__ import annotations
from collections import Counter, defaultdict, deque
from dataclasses import dataclass
from math import comb
from typing import Sequence
from .linalg import bareiss, signed_laplacian

SMOOTHINGS = (((0, 1), (2, 3)), ((0, 3), (1, 2)))


class DSU:
    def __init__(self, n):
        self.p = list(range(n))
        self.size = [1] * n
    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x
    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a == b:
            return
        if self.size[a] < self.size[b]:
            a, b = b, a
        self.p[b] = a
        self.size[a] += self.size[b]


@dataclass(frozen=True)
class Diagram:
    pd: tuple[tuple[int, int, int, int], ...]
    free_circles: int = 0

    def __post_init__(self):
        if type(self.free_circles) is not int or self.free_circles < 0:
            raise ValueError("free_circles must be a nonnegative integer")
        if any(len(c) != 4 or any(type(x) is not int for x in c) for c in self.pd):
            raise ValueError("crossings require four integer edge labels")
        counts = Counter(x for c in self.pd for x in c)
        if any(v != 2 for v in counts.values()):
            raise ValueError("each closed-diagram edge must occur twice")
        if not self.pd and not self.free_circles:
            raise ValueError("empty PD is ambiguous; supply free_circles")
        # The rotation system, not just the abstract graph, must be spherical.
        if self.pd:
            alpha = self.edge_involution()
            f = len(self.faces(alpha)[1])
            if f != len(self.pd) + 2 * self.shadow_components(alpha):
                raise ValueError("positive-genus PD rotation system is not classical")

    def edge_involution(self) -> list[int]:
        positions = defaultdict(list)
        for v, crossing in enumerate(self.pd):
            for s, label in enumerate(crossing):
                positions[label].append(4 * v + s)
        alpha = [0] * (4 * len(self.pd))
        for a, b in positions.values():
            alpha[a], alpha[b] = b, a
        return alpha

    @staticmethod
    def faces(alpha):
        face = [-1] * len(alpha)
        cycles = []
        for start in range(len(alpha)):
            if face[start] >= 0:
                continue
            cycle, d = [], start
            while face[d] < 0:
                face[d] = len(cycles)
                cycle.append(d)
                a = alpha[d]
                d = 4 * (a // 4) + (a + 1) % 4
            if d != start:
                raise ArithmeticError("bad face permutation")
            cycles.append(cycle)
        return face, cycles

    def shadow_components(self, alpha=None):
        if not self.pd:
            return 0
        alpha = self.edge_involution() if alpha is None else alpha
        dsu = DSU(len(self.pd))
        for d, a in enumerate(alpha):
            dsu.union(d // 4, a // 4)
        return len({dsu.find(v) for v in range(len(self.pd))})

    def state_circles(self, state: int) -> tuple[tuple[int, ...], ...]:
        if state < 0 or state >= 1 << len(self.pd):
            raise ValueError("state out of range")
        alpha = self.edge_involution()
        dsu = DSU(len(alpha))
        for d, a in enumerate(alpha):
            dsu.union(d, a)
        for v in range(len(self.pd)):
            for a, b in SMOOTHINGS[(state >> v) & 1]:
                dsu.union(4 * v + a, 4 * v + b)
        groups = defaultdict(list)
        for d in range(len(alpha)):
            groups[dsu.find(d)].append(d)
        circles = sorted((tuple(g) for g in groups.values()), key=lambda x: x[0])
        circles.extend((len(alpha) + j,) for j in range(self.free_circles))
        return tuple(circles)

    def orientation_data(self):
        alpha = self.edge_involution()
        outgoing = [None] * len(alpha)
        components = self.free_circles
        for start in range(len(alpha)):
            if outgoing[start] is not None:
                continue
            components += 1
            outgoing[start] = True
            queue = [start]
            while queue:
                d = queue.pop()
                opposite = 4 * (d // 4) + (d + 2) % 4
                for e in (alpha[d], opposite):
                    value = not outgoing[d]
                    if outgoing[e] is None:
                        outgoing[e] = value
                        queue.append(e)
                    elif outgoing[e] != value:
                        raise ValueError("orientation inconsistency")
        ones = 0
        for v in range(len(self.pd)):
            zeros_oriented = all(outgoing[4*v+a] != outgoing[4*v+b] for a,b in SMOOTHINGS[0])
            ones += not zeros_oriented
        return components, ones

    def euler_one(self) -> int:
        components, ones = self.orientation_data()
        return (-1 if ones % 2 else 1) * (1 << (components - 1))

    def tait_data(self):
        """Connected-shadow Tait graph and raw (-i)^phase prefactor."""
        if not self.pd or self.free_circles or self.shadow_components() != 1:
            raise ValueError("Tait formula here requires a nonempty connected shadow")
        alpha = self.edge_involution()
        face, cycles = self.faces(alpha)
        adj = [set() for _ in cycles]
        for d, a in enumerate(alpha):
            adj[face[d]].add(face[a])
            adj[face[a]].add(face[d])
        color = [None] * len(cycles)
        color[0] = 0
        queue = deque([0])
        while queue:
            f = queue.popleft()
            for g in adj[f]:
                if color[g] is None:
                    color[g] = 1 - color[f]
                    queue.append(g)
                elif color[g] == color[f]:
                    raise ValueError("not checkerboard colorable")
        if any(x is None for x in color):
            raise ArithmeticError("dual graph disconnected")
        black = {f: j for j, f in enumerate(f for f, c in enumerate(color) if c)}
        edges, total_b = [], 0
        for v in range(len(self.pd)):
            slots = [s for s in range(4) if color[face[4*v+s]]]
            if slots not in ([0, 2], [1, 3]):
                raise ArithmeticError("nonalternating corners")
            b = int(slots == [0, 2])
            total_b += b
            u, w = (black[face[4*v+s]] for s in slots)
            edges.append((u, w, -1 if b else 1))
        return len(black), edges, (total_b + len(black) - 1) % 4

    def euler_i(self) -> tuple[int, int]:
        if not self.pd:
            return (1, 0) if self.free_circles == 1 else (0, 0)
        if self.free_circles or self.shadow_components() != 1:
            return (0, 0)
        v, edges, phase = self.tait_data()
        lap = signed_laplacian(v, edges)
        value = bareiss([row[1:] for row in lap[1:]])
        unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[phase]
        return value * unit[0], value * unit[1]

    def shadow_four(self) -> tuple[int, int, int, int]:
        """Euler Laurent polynomial modulo q^4-1, without enumerating states."""
        e = self.euler_one()
        z = self.euler_i()
        parity = (len(self.state_circles(0)) - 1) % 2
        if z[1 - parity]:
            raise ArithmeticError("Jones parity mismatch")
        d = z[parity]
        if (e + d) % 2 or (e - d) % 2:
            raise ArithmeticError("nonintegral residue reconstruction")
        result = [0] * 4
        result[parity], result[parity + 2] = (e + d) // 2, (e - d) // 2
        return tuple(result)

    def cube_polynomial(self, max_crossings=18) -> dict[int, int]:
        """Independent exponential state-sum oracle, NOT the fast path."""
        n = len(self.pd)
        if n > max_crossings:
            raise ValueError("reference cube budget exceeded")
        result = defaultdict(int)
        for s in range(1 << n):
            h = s.bit_count()
            c = len(self.state_circles(s)) - 1
            for j in range(c + 1):
                result[h + c - 2*j] += (-1 if h % 2 else 1) * comb(c, j)
        return {q: a for q, a in sorted(result.items()) if a}


def from_braid(strands: int, word: Sequence[int]) -> Diagram:
    if type(strands) is not int or strands < 1:
        raise ValueError("invalid strand count")
    if any(type(g) is not int or not 0 < abs(g) < strands for g in word):
        raise ValueError("invalid braid generator")
    top = list(range(strands))
    current = top.copy()
    next_label = strands
    pd = []
    for g in word:
        j = abs(g) - 1
        tl, tr = current[j:j+2]
        bl, br = next_label, next_label + 1
        next_label += 2
        # Positive generator has oriented smoothing zero.
        pd.append((tr, br, bl, tl) if g > 0 else (tl, tr, br, bl))
        current[j:j+2] = [bl, br]
    dsu = DSU(next_label)
    for a, b in zip(top, current):
        dsu.union(a, b)
    used = {dsu.find(x) for c in pd for x in c}
    free = len({dsu.find(x) for x in top} - used)
    names = {x: j for j, x in enumerate(sorted(used))}
    return Diagram(tuple(tuple(names[dsu.find(x)] for x in c) for c in pd), free)


def complete_matching(suffix_pd: Sequence[Sequence[int]], pairs: Sequence[Sequence[int]]) -> Diagram:
    counts = Counter(x for c in suffix_pd for x in c)
    if not suffix_pd or any(v not in (1, 2) for v in counts.values()):
        raise ValueError("need a nonempty valid suffix")
    boundary = {x for x, c in counts.items() if c == 1}
    flat = [x for pair in pairs for x in pair]
    if any(len(pair) != 2 for pair in pairs) or len(flat) != len(set(flat)) or set(flat) != boundary:
        raise ValueError("matching does not cover suffix boundary exactly")
    labels = {x: j for j, x in enumerate(sorted(counts))}
    dsu = DSU(len(labels))
    for a, b in pairs:
        dsu.union(labels[a], labels[b])
    return Diagram(tuple(tuple(dsu.find(labels[x]) for x in c) for c in suffix_pd))
