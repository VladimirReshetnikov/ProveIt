"""Finite-field contraction, truncation, and exterior representatives.

Only oriented DUAL-GRAPH incidences enter this module. The unsigned geometric
matrix is never reduced modulo a field. Raw decomposable exterior vectors are
kept separately from Gaussian-eliminated basis rows.
"""
from __future__ import annotations
from math import isqrt
from .model import Instance


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def choose_prime(q: int, b: int) -> int:
    p = max(101, 2 * (q + b) + 1)
    while not is_prime(p):
        p += 1
    return p


def vector_basis(vectors, p: int) -> dict[int, list[int]]:
    basis = {}
    for raw in vectors:
        v = [x % p for x in raw]
        for pivot in sorted(basis):
            if v[pivot]:
                c = v[pivot]
                v = [(x - c * y) % p for x, y in zip(v, basis[pivot])]
        pivot = next((i for i, x in enumerate(v) if x), None)
        if pivot is not None:
            inv = pow(v[pivot], -1, p)
            basis[pivot] = [x * inv % p for x in v]
    return basis


def vector_rank(vectors, p: int) -> int:
    return len(vector_basis(vectors, p))


def incidence_vectors(inst: Instance, p: int) -> list[list[int]]:
    r = inst.vertices - 1
    answer = []
    for u, v in inst.edges:
        x = [0] * r
        if u:
            x[u - 1] += 1
        if v:
            x[v - 1] -= 1
        answer.append([a % p for a in x])
    return answer


def sample_representation(inst: Instance, groups, b: int, p: int, rng):
    """Return rank-b images, or None if the sampled mandatory columns lose rank."""
    vectors = incidence_vectors(inst, p)
    r = inst.vertices - 1
    y = []
    for group in groups:
        row = [0] * r
        for e in sorted(group):
            c = rng.randrange(p)
            row = [(a + c * t) % p for a, t in zip(row, vectors[e])]
        y.append(row)
    basis = vector_basis(y, p)
    if len(basis) != len(groups):
        return None
    free = [i for i in range(r) if i not in basis]
    quotient = []
    for raw in vectors:
        v = list(raw)
        for pivot in sorted(basis):
            c = v[pivot]
            if c:
                v = [(x - c * t) % p for x, t in zip(v, basis[pivot])]
        quotient.append([v[i] for i in free])
    projection = [[rng.randrange(p) for _ in free] for _ in range(min(b, len(free)))]
    return [tuple(sum(x * y for x, y in zip(row, v)) % p for row in projection)
            for v in quotient]


def wedge_extend(raw: dict[int, int], vector, p: int) -> dict[int, int]:
    """Append a vector on the right of an exterior product in the sorted basis."""
    out = {}
    for mask, c in raw.items():
        for j, value in enumerate(vector):
            bit = 1 << j
            if mask & bit or not value:
                continue
            sign = -1 if (mask >> (j + 1)).bit_count() % 2 else 1
            target = mask | bit
            out[target] = (out.get(target, 0) + sign * c * value) % p
    return {mask: value for mask, value in out.items() if value}


class ExteriorBasis:
    def __init__(self, p: int):
        self.p = p
        self.rows: dict[int, dict[int, int]] = {}
        self.witnesses: list[tuple[dict[int, int], tuple[int, ...]]] = []
        self.seen_sets: set[tuple[int, ...]] = set()  # Literal-set ablation only.

    def add(self, raw: dict[int, int], witness: tuple[int, ...]) -> bool:
        v = dict(raw)
        p = self.p
        for pivot in sorted(self.rows):
            c = v.get(pivot, 0)
            if not c:
                continue
            for j, x in self.rows[pivot].items():
                value = (v.get(j, 0) - c * x) % p
                if value:
                    v[j] = value
                else:
                    v.pop(j, None)
        if not v:
            return False
        pivot = min(v)
        inv = pow(v[pivot], -1, p)
        self.rows[pivot] = {j: x * inv % p for j, x in v.items()}
        # Never extend the eliminated row: it may be a nondecomposable sum.
        self.witnesses.append((dict(raw), witness))
        return True
