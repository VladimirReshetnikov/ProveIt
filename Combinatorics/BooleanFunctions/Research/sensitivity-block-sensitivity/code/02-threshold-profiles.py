#!/usr/bin/env python3
"""Exact threshold-resolved sensitivity upper bounds (standard library only).

These are proved upper bounds, not an algorithm for computing the sensitivity
of an arbitrary Boolean function. Integers are unbounded Python integers.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass
from functools import lru_cache
from math import comb
from typing import Any

@dataclass(frozen=True)
class Parameters:
    depth: int = 16
    degree: int = 14_400_000_000
    positions: int = 4
    forbidden: int = 34
    base_blocks: int = 30_000
    copies: int = 62_500

    def __post_init__(self) -> None:
        for key, value in asdict(self).items():
            if type(value) is not int or value < 1:
                raise ValueError(f"{key} must be a positive integer")
        if self.forbidden < 4:
            raise ValueError("The gate-count formulas require forbidden >= 4")

    @property
    def rows(self) -> int:
        return 2 * self.degree + 1

    @property
    def block_length(self) -> int:
        return self.depth + 2


def label_certificate(p: Parameters) -> tuple[int, int]:
    """Admissible labels exist when the returned numerator < denominator."""
    t = p.forbidden
    return comb(p.rows, t), p.positions ** (t * (t - 3) // 2)


def transfer(a: int, b: int, c: int, t: int) -> int:
    """Candidate-list bound for one, two, or three gate-repair clauses."""
    return max((t - 1) * a + b,
               (t - 2) * a + b + c,
               (t - 4) * a + 3 * c)


def compute_profiles(p: Parameters, *, packing: bool = True,
                     clipping: bool = True) -> list[dict[str, Any]]:
    """Return every certified profile. Slot zero is deliberately unused.

    packing=False is a valid ablation: use the older separate T/G budgets.
    clipping=False omits valid interval-containment improvements.
    """
    H = p.depth + 1
    N0 = p.block_length * p.base_blocks
    s0 = [0] + [H - q + 1 for q in range(1, H + 1)]
    s1 = [0] + [N0 - H + q for q in range(1, H + 1)]
    j0 = [[0] * (H + 1) for _ in range(H + 1)]
    j1 = [[0] * (H + 1) for _ in range(H + 1)]
    layers = [dict(level=0, H=H, s0=s0, s1=s1, j0=j0, j1=j1)]
    for ell in range(1, p.depth + 1):
        Q, H = H, H - 1
        a, target = s0[Q], p.positions * s1[Q]
        n0, n1 = [0] * (H + 1), [0] * (H + 1)
        m0 = [[0] * (H + 1) for _ in range(H + 1)]
        m1 = [[0] * (H + 1) for _ in range(H + 1)]
        for q in range(1, H + 1):
            g = Q - q
            if packing:
                n0[q] = transfer(a, s1[g], j1[g][Q], p.forbidden)
            else:
                n0[q] = (p.forbidden - 1) * a + max(
                    s1[g] + j1[g][Q], 3 * j1[g][Q])
            n1[q] = p.degree * s0[g] + target
            for qp in range(q + 1, H + 1):
                gp = Q - qp
                u, v = j1[gp][g], j1[gp][Q]
                if packing:
                    m0[q][qp] = transfer(a, u, v, p.forbidden)
                else:
                    m0[q][qp] = (p.forbidden - 1) * a + max(u + v, 3 * v)
                m1[q][qp] = p.degree * j0[gp][g] + target
        if clipping:
            for gap in range(1, H):
                for q in range(1, H - gap + 1):
                    qp = q + gap
                    for mat, single in ((m0, n0), (m1, n1)):
                        bound = min(mat[q][qp], single[q], single[qp])
                        if gap > 1:
                            bound = min(bound, mat[q + 1][qp], mat[q][qp - 1])
                        mat[q][qp] = bound
        s0, s1, j0, j1 = n0, n1, m0, m1
        layers.append(dict(level=ell, H=H, s0=s0, s1=s1, j0=j0, j1=j1))
    return layers


class IndependentVerifier:
    """An independent memoized implementation of the mathematical recurrence.

    It uses a DAG of single/pair requests instead of the production array loop.
    This checks arithmetic/data flow; it is not proof-assistant verification.
    """
    def __init__(self, p: Parameters):
        self.p = p

    @lru_cache(maxsize=None)
    def single(self, ell: int, bit: int, q: int) -> int:
        p = self.p
        if ell == 0:
            H = p.depth + 1
            return H - q + 1 if bit == 0 else p.block_length * p.base_blocks - H + q
        Q = p.depth + 2 - ell
        g = Q - q
        if bit == 1:
            return (p.degree * self.single(ell - 1, 0, g)
                    + p.positions * self.single(ell - 1, 1, Q))
        a = self.single(ell - 1, 0, Q)
        b = self.single(ell - 1, 1, g)
        c = self.joint(ell - 1, 1, g, Q)
        # Deliberately expand the formula instead of calling transfer().
        return max((p.forbidden - 1) * a + b,
                   (p.forbidden - 2) * a + b + c,
                   (p.forbidden - 4) * a + 3 * c)

    @lru_cache(maxsize=None)
    def joint(self, ell: int, bit: int, q: int, qp: int) -> int:
        if not q < qp:
            raise ValueError("A joint profile needs q < qp")
        if ell == 0:
            return 0
        p = self.p
        Q = p.depth + 2 - ell
        gp, g = Q - qp, Q - q
        if bit == 1:
            raw = (p.degree * self.joint(ell - 1, 0, gp, g)
                   + p.positions * self.single(ell - 1, 1, Q))
        else:
            a = self.single(ell - 1, 0, Q)
            b = self.joint(ell - 1, 1, gp, g)
            c = self.joint(ell - 1, 1, gp, Q)
            raw = max((p.forbidden - 1) * a + b,
                      (p.forbidden - 2) * a + b + c,
                      (p.forbidden - 4) * a + 3 * c)
        candidates = [raw, self.single(ell, bit, q), self.single(ell, bit, qp)]
        if qp - q > 1:
            candidates += [self.joint(ell, bit, q + 1, qp),
                           self.joint(ell, bit, q, qp - 1)]
        return min(candidates)

    def check_all(self, layers: list[dict[str, Any]]) -> int:
        count = 0
        for layer in layers:
            ell, H = layer["level"], layer["H"]
            for bit in (0, 1):
                for q in range(1, H + 1):
                    assert layer[f"s{bit}"][q] == self.single(ell, bit, q)
                    count += 1
                    for qp in range(q + 1, H + 1):
                        assert layer[f"j{bit}"][q][qp] == self.joint(ell, bit, q, qp)
                        count += 1
        return count


def summarize(p: Parameters, layers: list[dict[str, Any]]) -> dict[str, int]:
    a, b = layers[-1]["s0"][1], layers[-1]["s1"][1]
    A = max(p.copies * a, b)
    beta = p.copies * p.base_blocks * p.rows ** p.depth
    W = p.block_length * p.positions ** p.depth
    return dict(root_s0=a, root_s1=b, A=A, beta=beta, W=W, n=beta * W)
