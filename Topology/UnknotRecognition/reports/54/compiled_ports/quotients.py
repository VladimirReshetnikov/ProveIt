"""Exact monotone full-port quotients, with lazy multiplicity collapse.

Only coning ENTIRE unions of fixed source atoms is supported. Arbitrary
pointwise attachment maps are deliberately outside this API.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from collections import defaultdict
from .profiles import Profiles


def atom_group(atoms, m):
    atoms = tuple(atoms)
    if any(type(j) is not int or not 0 <= j < m for j in atoms):
        raise ValueError('atom indices must be in range')
    return tuple(sorted(set(atoms)))


class QuotientEngine:
    def __init__(self, profiles: Profiles):
        if not isinstance(profiles, Profiles):
            raise ValueError('validated profiles required')
        self.profiles = profiles
        self.s, self.m = len(profiles.rows), len(profiles.lengths)
        self.parent = list(range(self.s + self.m))
        self.rank = [0] * len(self.parent)
        self.real = [False] * len(self.parent)
        self.active_type = [False] * self.s
        self.active_atom = [False] * self.m
        adjacency = [[] for _ in range(self.m)]
        for i, row in enumerate(profiles.rows):
            for j, count in enumerate(row.counts):
                if count:
                    adjacency[j].append(i)
        self.adjacency = tuple(tuple(a) for a in adjacency)
        self.count = profiles.orbit_count
        self.stats = dict(activated_types=0, activated_atoms=0, incidence_edges=0,
                          union_attempts=0, effective_unions=0, cones=0)

    def clone(self):
        obj = object.__new__(type(self))
        for key, value in self.__dict__.items():
            setattr(obj, key, value.copy() if isinstance(value, (list, dict)) else value)
        return obj

    def _find(self, x):
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def _union(self, a, b):
        self.stats['union_attempts'] += 1
        a, b = self._find(a), self._find(b)
        if a == b:
            return
        self.stats['effective_unions'] += 1
        if self.real[a] and self.real[b]:
            self.count -= 1
        if self.rank[a] < self.rank[b]:
            a, b = b, a
        self.parent[b] = a
        self.real[a] = self.real[a] or self.real[b]
        if self.rank[a] == self.rank[b]:
            self.rank[a] += 1

    def _activate(self, j):
        if self.active_atom[j]:
            return
        self.active_atom[j] = True
        self.stats['activated_atoms'] += 1
        for i in self.adjacency[j]:
            self.stats['incidence_edges'] += 1
            if not self.active_type[i]:
                self.active_type[i] = True
                self.real[i] = True  # an inactive type has never been joined
                self.count -= self.profiles.rows[i].multiplicity - 1
                self.stats['activated_types'] += 1
            self._union(self.s + j, i)

    def cone(self, atoms):
        group = atom_group(atoms, self.m)  # validate before mutating state
        self.stats['cones'] += 1
        for j in group:
            self._activate(j)
        for a, b in zip(group, group[1:]):
            self._union(self.s + a, self.s + b)
        return self.count

    def apply_blocks(self, blocks):
        # Materialize/validate the complete update before the first mutation.
        groups = tuple(atom_group(g, self.m) for g in blocks)
        for group in groups:
            self.cone(group)
        return self.count

    def census(self):
        histogram = defaultdict(int)
        sums = {}
        for i, row in enumerate(self.profiles.rows):
            if not self.active_type[i]:
                histogram[row.counts] += row.multiplicity
            else:
                root = self._find(i)
                mass = sums.setdefault(root, [0] * self.m)
                for j, value in enumerate(row.counts):
                    mass[j] += row.multiplicity * value
        for value in sums.values():
            histogram[tuple(value)] += 1
        result = Profiles.from_histogram(self.profiles.lengths, histogram)
        if result.orbit_count != self.count:
            raise ArithmeticError('incremental count and reconstructed census disagree')
        return result
