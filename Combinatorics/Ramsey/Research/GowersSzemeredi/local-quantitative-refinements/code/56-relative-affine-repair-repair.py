#!/usr/bin/env python3
"""Exact modal affine decoder on explicit finite abelian groups.

This is a reference implementation, not a sublinear oracle algorithm.
Weights are rational. Labels lie in an explicitly represented finite abelian
product group. The accompanying paper proves a more general target-group result.
Only Python's standard library is required.
"""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Iterable, Sequence

Element = tuple[int, ...]

@dataclass(frozen=True)
class AbelianGroup:
    moduli: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.moduli or any(not isinstance(m, int) or m < 1 for m in self.moduli):
            raise ValueError("moduli must be a nonempty tuple of positive integers")

    @property
    def elements(self) -> tuple[Element, ...]:
        return tuple(product(*(range(m) for m in self.moduli)))

    @property
    def zero(self) -> Element:
        return tuple(0 for _ in self.moduli)

    def contains(self, x: Element) -> bool:
        return len(x) == len(self.moduli) and all(0 <= a < m for a, m in zip(x, self.moduli))

    def add(self, x: Element, y: Element) -> Element:
        return tuple((a + b) % m for a, b, m in zip(x, y, self.moduli))

    def sub(self, x: Element, y: Element) -> Element:
        return tuple((a - b) % m for a, b, m in zip(x, y, self.moduli))


def mode(histogram: dict[Element, F], default: Element) -> Element:
    """Deterministic lexicographic tie-breaking; zero mass uses default."""
    if not histogram:
        return default
    return min(histogram, key=lambda v: (-histogram[v], v))


def decode(domain: AbelianGroup, target: AbelianGroup,
           weights: Sequence[F | int], labels: Sequence[Element]) -> dict:
    """Return a candidate, exact test defect, and independently checked status.

    Output `certified_by_main_theorem` means the *numerical hypotheses* in the
    manuscript hold and the output was checked directly. It is not a proof-
    assistant certificate. Off-support labels are ignored in the first stage.
    Complexity is O(N^2) group/hash operations, plus rational arithmetic cost.
    """
    xs = domain.elements
    n = len(xs)
    if len(weights) != n or len(labels) != n:
        raise ValueError("weights and labels must have one entry per domain element")
    w = tuple(F(a) for a in weights)
    if any(a < 0 or a > 1 for a in w) or sum(w) == 0:
        raise ValueError("weights must lie in [0,1] and have positive total mass")
    if any(not target.contains(v) for v in labels):
        raise ValueError("a label is not a canonical target-group element")
    idx = {x: i for i, x in enumerate(xs)}
    q: list[Element] = []
    r: list[F] = []
    defect = F(0)
    pair_error = F(0)
    for h in xs:
        hist: dict[Element, F] = defaultdict(F)
        for i, x in enumerate(xs):
            j = idx[domain.add(x, h)]
            mass = w[i] * w[j]
            if mass:
                hist[target.sub(labels[j], labels[i])] += mass
        total = sum(hist.values(), F(0))
        chosen = mode(hist, target.zero)
        q.append(chosen)
        r.append(total / n)
        defect += (total * total - sum((a*a for a in hist.values()), F(0))) / n**3
        pair_error += (total - hist.get(chosen, F(0))) / n**2
    alpha = sum(w) / n
    energy = sum((a*a for a in r), F(0)) / n
    uniformity_fourth = energy - alpha**4
    epsilon = defect / energy
    L: list[Element] = []
    for x in xs:
        hist = defaultdict(F)
        for i, y in enumerate(xs):
            j = idx[domain.add(x, y)]
            hist[target.sub(q[j], q[i])] += 1
        L.append(mode(hist, target.zero))
    residual = defaultdict(F)
    for wi, label, li in zip(w, labels, L):
        if wi:
            residual[target.sub(label, li)] += wi
    c = mode(residual, target.zero)
    phi = tuple(target.add(li, c) for li in L)
    distance = sum((wi for wi, a, b in zip(w, labels, phi) if a != b), F(0)) / sum(w)
    additive = all(L[idx[domain.add(x,y)]] == target.add(L[i], L[j])
                   for i,x in enumerate(xs) for j,y in enumerate(xs))
    rho = F(sum(q[idx[domain.add(x,y)]] != target.add(q[i],q[j])
                for i,x in enumerate(xs) for j,y in enumerate(xs)), n*n)
    tau = F(sum(a != b for a,b in zip(q,L)), n)
    hypotheses = uniformity_fourth <= alpha**5 / 1024 and epsilon <= F(1,1024)
    direct_check = additive and distance <= F(13,50)*epsilon
    if hypotheses and not direct_check:
        raise ArithmeticError("A hypothesis-satisfying input contradicts the claimed decoder bound")
    return dict(alpha=alpha, energy=energy, uniformity_fourth=uniformity_fourth,
                epsilon=epsilon, pair_error=pair_error, r=tuple(r),
                q=tuple(q), L=tuple(L), c=c, affine_candidate=phi,
                distance=distance, additive=additive, rho=rho, tau=tau,
                hypotheses_hold=hypotheses,
                certified_by_main_theorem=hypotheses and direct_check)


def json_ready(value):
    """Serialize rationals as exact numerator/denominator strings."""
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: json_ready(v) for k,v in value.items()}
    if isinstance(value, (tuple,list)):
        return [json_ready(v) for v in value]
    return value

if __name__ == "__main__":
    import json
    G, H = AbelianGroup((31,)), AbelianGroup((3,))
    w = [F(1)]*31
    w[0] = F(1,10000)
    labels = [(1,)]+[(0,)]*30
    result = decode(G,H,w,labels)
    print(json.dumps(json_ready({k:v for k,v in result.items()
          if k not in {'q','L','r','affine_candidate'}}), indent=2))
