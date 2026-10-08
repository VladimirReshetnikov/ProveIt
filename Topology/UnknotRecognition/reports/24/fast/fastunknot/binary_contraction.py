"""Packed scalar contraction reused from the preceding triangular-transfer draft.

Frozen reference SHA-256:
8c264b87892289c23852241614567528e862cba730da5d572adaae34def25ba2.
The original reference is supplied with the research package.  This module
retains its scalar basis convention so transfer outputs can be compared exactly.
"""
from __future__ import annotations

from collections import defaultdict

from fastunknot.scan_fast import FastScan


def bits(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


class BinaryBasis:
    def __init__(self):
        self.pivots = {}

    def add(self, vector, coordinates=0):
        while vector:
            top = vector.bit_length() - 1
            old = self.pivots.get(top)
            if old is None:
                self.pivots[top] = vector, coordinates
                return True
            vector ^= old[0]
            coordinates ^= old[1]
        return False

    def solve(self, vector):
        coordinates = 0
        while vector:
            top = vector.bit_length() - 1
            old = self.pivots.get(top)
            if old is None:
                raise ArithmeticError("incomplete scalar basis")
            vector ^= old[0]
            coordinates ^= old[1]
        return coordinates


def xor_entry(row, target, value):
    if value:
        new = row.get(target, 0) ^ value
        if new:
            row[target] = new
        else:
            row.pop(target, None)


def binary_contraction(scan):
    """Return a special contraction of d0, using group-local bit matrices.

    I columns are bit masks on old objects. P and H columns are bit masks on
    survivors and old objects respectively. All coefficients are typed scalar
    identities; H lowers homological degree and preserves matching and q.
    """
    groups = defaultdict(list)
    for a, matching in enumerate(scan.mid):
        if matching is not None:
            groups[matching, scan.qshift[a], scan.deg[a]].append(a)
    keys = sorted(groups)
    images, lifts, kernels = {}, {}, {}
    for key in keys:
        scan._check()
        matching, quantum, degree = key
        sources = groups[key]
        targets = groups.get((matching, quantum, degree + 1), ())
        target_index = {v: i for i, v in enumerate(targets)}
        basis = BinaryBasis()
        nullspace = []
        for i, a in enumerate(sources):
            if not i & 255:
                scan._check()
            vector = 0
            for b, value in scan.out[a].items():
                if scan.qshift[b] == quantum:
                    if scan.mid[b] != matching or value != 1:
                        raise ArithmeticError("weight-zero map is not a typed identity")
                    vector ^= 1 << target_index[b]
            coordinates = 1 << i
            while vector:
                top = vector.bit_length() - 1
                old = basis.pivots.get(top)
                if old is None:
                    basis.pivots[top] = vector, coordinates
                    break
                vector ^= old[0]
                coordinates ^= old[1]
            if not vector:
                nullspace.append(coordinates)
        ordered = [basis.pivots[top] for top in sorted(basis.pivots)]
        images[key] = [pair[0] for pair in ordered]
        lifts[key] = [pair[1] for pair in ordered]
        kernels[key] = nullspace

    size = len(scan.mid)
    i_cols, p_cols, h_cols = [], [0] * size, [0] * size
    survivor_mid, survivor_deg, survivor_q = [], [], []
    for key in keys:
        scan._check()
        matching, quantum, degree = key
        vertices = groups[key]
        prev = matching, quantum, degree - 1
        boundaries = images.get(prev, [])
        independent = BinaryBasis()
        for v in boundaries:
            if not independent.add(v):
                raise ArithmeticError("dependent boundary basis")
        reps = []
        for v in kernels[key]:
            if independent.add(v):
                reps.append(v)
        basis_vectors = boundaries + reps + lifts[key]
        if len(basis_vectors) != len(vertices):
            raise ArithmeticError("d0 is not a chain differential")
        inverse = BinaryBasis()
        for i, v in enumerate(basis_vectors):
            if not inverse.add(v, 1 << i):
                raise ArithmeticError("scalar chain decomposition is singular")
        offset = len(i_cols)
        for v in reps:
            i_cols.append(sum(1 << vertices[j] for j in bits(v)))
            survivor_mid.append(matching)
            survivor_deg.append(degree)
            survivor_q.append(quantum)
        prev_vertices = groups.get(prev, ())
        prev_lifts = lifts.get(prev, ())
        bcount, rcount = len(boundaries), len(reps)
        for j, a in enumerate(vertices):
            if not j & 255:
                scan._check()
            coordinates = inverse.solve(1 << j)
            p_cols[a] = ((coordinates >> bcount) & ((1 << rcount) - 1)) << offset
            local_h = 0
            for b in bits(coordinates & ((1 << bcount) - 1)):
                local_h ^= prev_lifts[b]
            h_cols[a] = sum(1 << prev_vertices[b] for b in bits(local_h))
    return dict(i=i_cols, p=p_cols, h=h_cols, mid=survivor_mid,
                deg=survivor_deg, q=survivor_q)

