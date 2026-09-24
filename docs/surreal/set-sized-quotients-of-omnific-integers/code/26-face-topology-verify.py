#!/usr/bin/env python3
"""Finite exact checks for Face Topology and Arithmetic Homology.

Only finite rational incidence calculations are checked here. This program is
not a proof of the statements about infinite monoid rings or surreal classes.
Python 3.10+; standard library only. Output is written beside this script.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json
import random
import time

CHECKS = 0

def check(condition: bool, message: str) -> None:
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(message)


def rank(rows: list[list[int | Fraction]], ncols: int) -> int:
    a = [[Fraction(x) for x in row] for row in rows]
    lead = 0
    for col in range(ncols):
        pivot = next((i for i in range(lead, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[lead], a[pivot] = a[pivot], a[lead]
        q = a[lead][col]
        a[lead] = [x / q for x in a[lead]]
        for i in range(lead + 1, len(a)):
            q = a[i][col]
            if q:
                a[i] = [x - q*y for x, y in zip(a[i], a[lead])]
        lead += 1
        if lead == len(a):
            break
    return lead


class Cone:
    def __init__(self, name: str, dimensions: dict[int, int]):
        self.name = name
        self.dim = dimensions
        self.faces = sorted(dimensions, key=lambda f: (dimensions[f], f))
        self.top = max(self.faces, key=lambda f: dimensions[f])
        self.d = dimensions[self.top]
        self.rays = [f for f in self.faces if dimensions[f] == 1]
        self.cache: dict[int, int] = {0: 0}
        check(dimensions.get(0) == 0, name + ': origin')
        for f in self.faces:
            for g in self.faces:
                check(f & g in dimensions, name + ': face intersections')
                if f != g and f & g == f:
                    check(dimensions[f] < dimensions[g], name + ': strict ranks')

    def join(self, bits: int) -> int:
        if bits not in self.cache:
            result = self.top
            for f in self.faces:
                if bits & f == bits:
                    result &= f
            check(result in self.dim, self.name + ': joins exist')
            self.cache[bits] = result
        return self.cache[bits]


def orthant(d: int) -> Cone:
    return Cone(f'orthant_{d}', {m: m.bit_count() for m in range(1 << d)})


def polygon(n: int) -> Cone:
    dims = {0: 0, (1 << n) - 1: 3}
    dims.update({1 << i: 1 for i in range(n)})
    dims.update({(1 << i) | (1 << ((i+1) % n)): 2 for i in range(n)})
    return Cone(f'polygon_cone_{n}', dims)


def cube(n: int) -> Cone:
    vertices = list(product((-1, 1), repeat=n))
    dims = {0: 0}
    for pattern in product((-1, 0, 1), repeat=n):
        mask = sum(1 << j for j, v in enumerate(vertices)
                   if all(p == 0 or p == x for p, x in zip(pattern, v)))
        dims[mask] = pattern.count(0) + 1
    return Cone(f'cube_cone_{n}', dims)


def octahedron() -> Cone:
    dims = {0: 0, 63: 4}
    for m in range(1, 64):
        if all((m & (3 << (2*i))) != (3 << (2*i)) for i in range(3)):
            dims[m] = m.bit_count()
    return Cone('octahedron_cone', dims)


def labels_for(cone: Cone, generators: tuple[int, ...]) -> dict[int, int]:
    labels = {0: 0}
    for s in range(1, 1 << len(generators)):
        i = (s & -s).bit_length() - 1
        labels[s] = cone.join(labels[s ^ (1 << i)] | generators[i])
    return labels


def boundary(source: list[int], target: list[int]) -> list[list[int]]:
    pos = {s: i for i, s in enumerate(target)}
    out = [[0] * len(source) for _ in target]
    for j, s in enumerate(source):
        bits = [i for i in range(s.bit_length()) if s >> i & 1]
        for k, i in enumerate(bits):
            t = s ^ (1 << i)
            if t in pos:
                out[pos[t]][j] = (-1) ** k
    return out


def diagonal_betti(cone: Cone, generators: tuple[int, ...],
                   independently_check: bool = True) -> dict[tuple[int, int], int]:
    labels = labels_for(cone, generators)
    r = len(generators)
    result = {}
    for g in sorted(set(labels.values()) - {0}):
        chains = {p: [s for s, h in labels.items()
                      if h == g and s.bit_count() == p] for p in range(r+2)}
        ranks = {p: rank(boundary(chains[p], chains[p-1]), len(chains[p]))
                 for p in range(1, r+2)}
        for p in range(1, r+1):
            value = len(chains[p]) - ranks[p] - ranks[p+1]
            check(value >= 0, cone.name + ': nonnegative diagonal homology')
            if value:
                result[p, g] = value
            if independently_check:
                # Reduced simplicial homology of the proper-join complex.
                delta = {j: [s for s, h in labels.items()
                             if h != g and h & g == h and s.bit_count() == j+1]
                         for j in range(-1, r+1)}
                degree = p - 2
                n = len(delta[degree])
                outgoing = (rank(boundary(delta[degree], delta[degree-1]),
                                 len(delta[degree])) if degree >= 0 else 0)
                incoming = rank(boundary(delta[degree+1], delta[degree]),
                                len(delta[degree+1]))
                check(value == n - outgoing - incoming,
                      cone.name + ': independent reduced-homology formula')
    return result


def check_d_squared(matrices: dict[int, list[list[Fraction]]],
                    basis: dict[int, list[int]]) -> None:
    for p in range(2, max(basis)+1):
        for row in range(len(basis[p-2])):
            for col in range(len(basis[p])):
                value = sum(matrices[p-1][row][mid] * matrices[p][mid][col]
                            for mid in range(len(basis[p-1])))
                check(value == 0, 'compressed differential squares to zero')


def cancel_complex(cone: Cone, generators: tuple[int, ...], expected: dict) -> int:
    labels = labels_for(cone, generators)
    r = len(generators)
    subsets = {p: [s for s in labels if s.bit_count() == p] for p in range(r+1)}
    basis = {p: [labels[s] for s in subsets[p]] for p in subsets}
    matrices = {p: [[Fraction(x) for x in row]
                    for row in boundary(subsets[p], subsets[p-1])]
                for p in range(1, r+1)}
    cancellations = 0
    check_d_squared(matrices, basis)
    while True:
        pivot = next(((p, j, i) for p in range(2, r+1)
                      for j, g in enumerate(basis[p-1])
                      for i, h in enumerate(basis[p])
                      if g == h and matrices[p][j][i]), None)
        if pivot is None:
            break
        p, j, i = pivot
        old = matrices[p]
        q = old[j][i]
        matrices[p] = [[old[a][b] - old[a][i]*old[j][b]/q
                        for b in range(len(basis[p])) if b != i]
                       for a in range(len(basis[p-1])) if a != j]
        matrices[p-1] = [[x for b, x in enumerate(row) if b != j]
                          for row in matrices[p-1]]
        if p < r:
            matrices[p+1] = [row for a, row in enumerate(matrices[p+1]) if a != i]
        del basis[p][i]
        del basis[p-1][j]
        cancellations += 1
    check_d_squared(matrices, basis)
    actual = {}
    for p in range(1, r+1):
        for g in basis[p]:
            actual[p, g] = actual.get((p, g), 0) + 1
        for j, g in enumerate(basis[p-1]):
            for i, h in enumerate(basis[p]):
                if matrices[p][j][i]:
                    check(g != h and g & h == g, 'strictly decreasing labels')
    check(actual == expected, cone.name + ': cancellation multiplicities')
    return cancellations


def antichain(items: tuple[int, ...]) -> bool:
    return all(f & g not in (f, g) for f, g in combinations(items, 2))


def serialize_betti(cone: Cone, betti: dict) -> list[dict]:
    return [dict(degree=p, face_mask=g, face_dimension=cone.dim[g], multiplicity=n)
            for (p, g), n in sorted(betti.items())]


def main() -> None:
    started = time.monotonic()
    rng = random.Random(23092026)
    cones = [orthant(d) for d in range(1, 6)]
    cones += [polygon(n) for n in range(4, 9)]
    cones += [cube(3), octahedron()]
    cases = []
    total_antichains = 0
    total_face_quotients = 0
    total_cancellations = 0
    for cone in cones:
        tested = set()
        # Every face quotient, including the augmentation and identity cases.
        for f in cone.faces:
            generators = tuple(g for g in cone.rays if g & f != g)
            if not generators:
                expected_fd = max(cone.dim[g] for g in cone.faces if g & f == 0)
                check(expected_fd == 0, 'identity face quotient')
                total_face_quotients += 1
                continue
            beta = diagonal_betti(cone, generators)
            predicted = {(cone.dim[g], g): 1 for g in cone.faces if g and g & f == 0}
            check(beta == predicted, cone.name + ': full disjoint-face Betti formula')
            h = max(p for p, _ in beta)
            check(h == max(cone.dim[g] for g in cone.faces if g & f == 0),
                  cone.name + ': disjoint-face flat dimension')
            check(h == 1 if len(generators) == 1 else h >= 2,
                  cone.name + ': singleton flatness criterion')
            if f == 0 or cone.dim[f] == cone.d-1:
                totals = [1] + [sum(v for (p, _), v in beta.items() if p == j)
                                for j in range(1, h+1)]
                cases.append(dict(cone=cone.name, quotient_face=f,
                                  quotient_face_dimension=cone.dim[f],
                                  flat_dimension=h, betti_totals=totals))
            tested.add(generators)
            total_face_quotients += 1
        # Deterministic small antichains and seeded samples, not an exhaustive search.
        candidates = {(g,) for g in cone.faces if g}
        candidates.update(pair for pair in combinations([g for g in cone.faces if g], 2)
                          if antichain(pair))
        nonzero = [g for g in cone.faces if g]
        for _ in range(35):
            sample = tuple(sorted(rng.sample(nonzero, min(rng.randint(2, 5), len(nonzero)))))
            if antichain(sample):
                candidates.add(sample)
        for generators in sorted(candidates):
            if generators in tested:
                continue
            beta = diagonal_betti(cone, generators)
            h = max(p for p, _ in beta)
            check(1 <= h <= cone.d, cone.name + ': dimension bound')
            check(h == 1 if len(generators) == 1 else h >= 2,
                  cone.name + ': flat radical ideal criterion')
            for (p, g), value in beta.items():
                check(p <= cone.dim[g], cone.name + ': local dimension bound')
            total_antichains += 1
        # Audit scalar cancellation independently in a representative complex.
        if len(cone.rays) <= 6:
            generators = tuple(cone.rays)
            beta = diagonal_betti(cone, generators)
            total_cancellations += cancel_complex(cone, generators, beta)
        # Every facet has dimension-one quotient iff the cone is simplicial.
        facet_values = []
        for f in cone.faces:
            if cone.dim[f] == cone.d-1:
                facet_values.append(max(cone.dim[g] for g in cone.faces if g & f == 0))
        check(all(h == 1 for h in facet_values) == (len(cone.rays) == cone.d),
              cone.name + ': simpliciality characterization')
    # Exact rational cap checks for the isolating modules on cube cones.
    cap_checks = 0
    for n in range(1, 4):
        c = cube(n)
        vertices = [tuple(v)+(1,) for v in product((-1, 1), repeat=n)]
        normals = [tuple((sign if j == i else 0) for j in range(n))+(1,)
                   for i in range(n) for sign in (-1, 1)]
        def inner(a, b):
            return sum(x*y for x, y in zip(a, b))
        def point(face):
            return tuple(sum(v[j] for i, v in enumerate(vertices) if face >> i & 1)
                         for j in range(n+1))
        for g in c.faces:
            if not g:
                continue
            b = point(g)
            active_normals = [ell for ell in normals if inner(ell, b) > 0]
            for h in c.faces:
                if not h:
                    continue
                u = point(h)
                for exponent in (3, 6, 10):
                    q = Fraction(1, 2**exponent)
                    m = tuple(x-q*y for x, y in zip(b, u))
                    in_cone = all(inner(ell, m) >= 0 for ell in normals)
                    in_face = in_cone and all(inner(ell, m) == 0 for ell in normals
                                              if inner(ell, b) == 0)
                    below_caps = in_face and all(inner(ell, m) < inner(ell, b)
                                                   for ell in active_normals)
                    check(below_caps == (h == g), 'face-isolating cap calculation')
                    cap_checks += 1
    output = dict(status='PASS', exact_assertions=CHECKS,
                  face_quotients_checked=total_face_quotients,
                  additional_radical_antichains_checked=total_antichains,
                  cancelled_contractible_pairs=total_cancellations,
                  rational_cap_checks=cap_checks,
                  examples=cases,
                  scope='Finite exact rational incidence and cap checks only; not a formal proof of infinite-ring theorems.',
                  elapsed_seconds=round(time.monotonic()-started, 3))
    destination = Path(__file__).resolve().with_name('verification_results.json')
    destination.write_text(json.dumps(output, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k:v for k,v in output.items() if k != 'examples'}, indent=2))


if __name__ == '__main__':
    main()
