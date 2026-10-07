#!/usr/bin/env python3
"""Exact collision-aware energy inventories and deterministic rounding.

Standard library only.  Counts ordered tuples, with repeated labels allowed.
Arithmetic is exact (integers/Fraction).  The dense implementation is intended
as a transparent reference implementation, not an FFT-optimized package.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence

Scalar = int | Fraction
Element = tuple[int, ...]


def rational(value: object) -> Fraction:
    """Parse integers or rational strings; reject inexact floating inputs."""
    if isinstance(value, (int, Fraction, str)):
        return Fraction(value)
    raise TypeError("Use integers or rational strings, not floating-point probabilities")


@dataclass(frozen=True)
class FiniteAbelianGroup:
    moduli: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.moduli or any(not isinstance(q, int) or q < 1 for q in self.moduli):
            raise ValueError("moduli must be a nonempty tuple of positive integers")

    @property
    def size(self) -> int:
        return math.prod(self.moduli)

    @property
    def zero(self) -> Element:
        return (0,) * len(self.moduli)

    def normalize(self, x: Sequence[int]) -> Element:
        if len(x) != len(self.moduli):
            raise ValueError("element has incorrect dimension")
        return tuple(a % q for a, q in zip(x, self.moduli))

    def elements(self) -> list[Element]:
        return list(itertools.product(*(range(q) for q in self.moduli)))

    def index(self, x: Sequence[int]) -> int:
        if len(x) != len(self.moduli):
            raise ValueError("element has incorrect dimension")
        out = 0
        for a, q in zip(x, self.moduli):
            out = out * q + a % q
        return out

    def scale(self, k: int, x: Sequence[int]) -> Element:
        return tuple((k * a) % q for a, q in zip(x, self.moduli))

    def add(self, x: Sequence[int], y: Sequence[int]) -> Element:
        return tuple((a + b) % q for a, b, q in zip(x, y, self.moduli))


def stirling_second(n: int) -> list[list[int]]:
    S = [[0] * (n + 1) for _ in range(n + 1)]
    S[0][0] = 1
    for k in range(1, n + 1):
        for j in range(1, k + 1):
            S[k][j] = S[k - 1][j - 1] + j * S[k - 1][j]
    return S


def response_coefficients(p: Scalar, degree: int) -> list[Scalar]:
    """EGF coefficients h_k(p) of (exp(t)-1)/(1+p(exp(t)-1))."""
    p = rational(p)
    S = stirling_second(degree)
    h: list[Scalar] = [0] * (degree + 1)
    powers = [Fraction(1)] * max(degree, 1)
    factorials = [1] * (degree + 1)
    for j in range(1, degree):
        powers[j] = -p * powers[j - 1]
    for j in range(1, degree + 1):
        factorials[j] = j * factorials[j - 1]
    for k in range(1, degree + 1):
        h[k] = sum(powers[j - 1] * factorials[j] * S[k][j]
                   for j in range(1, k + 1))
    return h


class EnergyInventory:
    """A[a,b][g] = expected partial ordered energy at group difference g."""
    def __init__(self, group: FiniteAbelianGroup, order: int) -> None:
        if order < 1:
            raise ValueError("order must be positive")
        self.group, self.order = group, order
        self.elements = group.elements()
        self.A = {(a, b): [0] * group.size
                  for a in range(order + 1) for b in range(order + 1)}
        self.A[0, 0][0] = 1
        self.targets = sorted(self.A, key=lambda ab: sum(ab), reverse=True)
        self.weighted_shift_additions = 0

    def _shifts(self, g: Element) -> dict[int, list[int]]:
        return {k: [self.group.index(self.group.add(x, self.group.scale(k, g)))
                    for x in self.elements]
                for k in range(-self.order, self.order + 1)}

    def apply(self, g: Element, coefficients: Sequence[Scalar]) -> None:
        """Multiply by sum r_(a+b) u^[a] v^[b] [(a-b)g], in place.

        Its degree-zero coefficient must be one. Descending total degree is
        essential: every source row must still have its pre-update value.
        """
        if len(coefficients) < 2 * self.order + 1 or coefficients[0] != 1:
            raise ValueError("need coefficients through 2*order, with r_0=1")
        g = self.group.normalize(g)
        shifts = self._shifts(g)
        for a, b in self.targets:
            out = self.A[a, b]
            for c in range(a + 1):
                for d in range(b + 1):
                    if c + d == 0 or coefficients[c + d] == 0:
                        continue
                    coeff = math.comb(a, c) * math.comb(b, d) * coefficients[c + d]
                    src = self.A[a - c, b - d]
                    shift = shifts[c - d]
                    for ix, val in enumerate(src):
                        if val:
                            out[shift[ix]] += coeff * val
                            self.weighted_shift_additions += 1

    def add_label(self, g: Element, probability: Scalar) -> None:
        p = rational(probability)
        if not 0 <= p <= 1:
            raise ValueError("probabilities must lie in [0,1]")
        if p:
            self.apply(g, [1] + [p] * (2 * self.order))

    def energy(self) -> Scalar:
        return self.A[self.order, self.order][0]

    def derivative(self, g: Element, probability: Scalar) -> Scalar:
        s = self.order
        h = response_coefficients(probability, 2 * s)
        ans: Scalar = 0
        for c in range(s + 1):
            for d in range(s + 1):
                if c + d:
                    ix = self.group.index(self.group.scale(d - c, g))
                    ans += (math.comb(s, c) * math.comb(s, d) * h[c + d]
                            * self.A[s - c, s - d][ix])
        return ans

    def replace_probability(self, g: Element, p: Scalar, q: Scalar) -> None:
        h = response_coefficients(p, 2 * self.order)
        self.apply(g, [1] + [(q - p) * h[k] for k in range(1, 2 * self.order + 1)])


def build_inventory(group: FiniteAbelianGroup, labels: Sequence[Element],
                    probabilities: Sequence[Scalar], order: int) -> EnergyInventory:
    if len(labels) != len(probabilities):
        raise ValueError("label and probability lengths differ")
    out = EnergyInventory(group, order)
    for g, p in zip(labels, probabilities):
        out.add_label(g, p)
    return out


def deterministic_round(models: Sequence[tuple[FiniteAbelianGroup, Sequence[Element], Scalar]],
                        probabilities: Sequence[Scalar], order: int) -> dict:
    """Round a rational signed sum of energies without decreasing expectation.

    models contain (ambient group, one group image per label, coefficient).
    Labels are shared between models and must appear in the same order.
    """
    p = [rational(x) for x in probabilities]
    if any(not 0 <= x <= 1 for x in p):
        raise ValueError("probabilities outside [0,1]")
    if not models or any(len(labels) != len(p) for _, labels, _ in models):
        raise ValueError("models must be nonempty with consistent label counts")
    weights = [rational(w) for _, _, w in models]
    invs = [build_inventory(G, labels, p, order) for G, labels, _ in models]
    initial = sum(w * inv.energy() for w, inv in zip(weights, invs))
    value = initial
    trace = []
    for i, old in enumerate(p):
        if old in (0, 1):
            continue
        deriv = sum(w * inv.derivative(labels[i], old)
                    for w, inv, (_, labels, _) in zip(weights, invs, models))
        new = Fraction(int(deriv >= 0))
        predicted = value + (new - old) * deriv
        for inv, (_, labels, _) in zip(invs, models):
            inv.replace_probability(labels[i], old, new)
        value = sum(w * inv.energy() for w, inv in zip(weights, invs))
        assert value == predicted and value >= initial
        trace.append({"index": i, "old": str(old), "derivative": str(deriv),
                      "new": int(new), "objective": str(value)})
        p[i] = new
    return {"selected_indices": [i for i, x in enumerate(p) if x == 1],
            "initial_objective": initial, "final_objective": value,
            "trace": trace,
            "weighted_shift_additions": sum(x.weighted_shift_additions for x in invs)}


def falling_ratio(r: int, n: int, j: int) -> Fraction:
    if not 0 <= r <= n or j < 0:
        raise ValueError("invalid hypergeometric parameters")
    if j > r:
        return Fraction(0)
    if j == 0:
        return Fraction(1)
    return Fraction(math.comb(r, j), math.comb(n, j))


class SupportInventory:
    """Exact support profiles for uniform fixed-cardinality rounding.

    A[a,b][j][g] counts tuples using exactly j distinct undecided labels.
    Already selected labels do not contribute to j.
    """
    def __init__(self, group: FiniteAbelianGroup, order: int) -> None:
        if order < 1:
            raise ValueError("order must be positive")
        self.group, self.order, self.degree = group, order, 2 * order
        self.elements = group.elements()
        self.A = {(a, b): [[0] * group.size for _ in range(self.degree + 1)]
                  for a in range(order + 1) for b in range(order + 1)}
        self.A[0, 0][0][0] = 1
        self.targets = sorted(self.A, key=lambda ab: sum(ab), reverse=True)

    def branch_coefficients(self, include: bool) -> list[list[int]]:
        m = self.degree
        S = stirling_second(m)
        R = [[0] * (m + 1) for _ in range(m + 1)]
        R[0][0] = 1
        for k in range(1, m + 1):
            for j in range(1, k + 1):
                h = (-1) ** (j - 1) * math.factorial(j) * S[k][j]
                R[k][j] -= h
                if include:
                    R[k][j - 1] += h
        return R

    def apply(self, g: Element, R: Sequence[Sequence[int]]) -> None:
        if R[0][0] != 1 or any(R[0][j] for j in range(1, self.degree + 1)):
            raise ValueError("constant term must be one")
        s, m = self.order, self.degree
        shifts = {k: [self.group.index(self.group.add(x, self.group.scale(k, g)))
                      for x in self.elements] for k in range(-s, s + 1)}
        for a, b in self.targets:
            for c in range(a + 1):
                for d in range(b + 1):
                    k = c + d
                    if not k:
                        continue
                    comb = math.comb(a, c) * math.comb(b, d)
                    shift = shifts[c - d]
                    for ell in range(k + 1):
                        coeff = comb * R[k][ell]
                        if not coeff:
                            continue
                        for j in range(a + b - k + 1):
                            out, src = self.A[a, b][j + ell], self.A[a - c, b - d][j]
                            for ix, val in enumerate(src):
                                if val:
                                    out[shift[ix]] += coeff * val

    def add_undecided(self, g: Element) -> None:
        R = [[0] * (self.degree + 1) for _ in range(self.degree + 1)]
        R[0][0] = 1
        for k in range(1, self.degree + 1):
            R[k][1] = 1
        self.apply(g, R)

    def add_included(self, g: Element) -> None:
        R = [[0] * (self.degree + 1) for _ in range(self.degree + 1)]
        for k in range(self.degree + 1):
            R[k][0] = 1
        self.apply(g, R)

    def expected(self, remaining: int, quota: int) -> Fraction:
        return sum((falling_ratio(quota, remaining, j) * self.A[self.order, self.order][j][0]
                    for j in range(self.degree + 1)), Fraction(0))

    def branch_expected(self, g: Element, remaining_after: int,
                        quota_after: int, include: bool) -> Fraction:
        """Probe only top-degree, zero-group-coordinate coefficients."""
        s, m = self.order, self.degree
        R = self.branch_coefficients(include)
        top = [self.A[s, s][j][0] for j in range(m + 1)]
        for c in range(s + 1):
            for d in range(s + 1):
                k = c + d
                if not k:
                    continue
                comb = math.comb(s, c) * math.comb(s, d)
                ix = self.group.index(self.group.scale(d - c, g))
                for ell in range(k + 1):
                    if not R[k][ell]:
                        continue
                    for j in range(m - k + 1):
                        top[j + ell] += comb * R[k][ell] * self.A[s - c, s - d][j][ix]
        return sum((falling_ratio(quota_after, remaining_after, j) * top[j]
                    for j in range(m + 1)), Fraction(0))


def fixed_size_round(models: Sequence[tuple[FiniteAbelianGroup, Sequence[Element], Scalar]],
                     order: int, size: int) -> dict:
    if not models:
        raise ValueError("at least one model is required")
    n = len(models[0][1])
    if any(len(labels) != n for _, labels, _ in models) or not 0 <= size <= n:
        raise ValueError("inconsistent models or invalid prescribed size")
    weights = [rational(w) for _, _, w in models]
    invs = [SupportInventory(G, order) for G, _, _ in models]
    for inv, (_, labels, _) in zip(invs, models):
        for g in labels:
            inv.add_undecided(g)
    remaining, quota = n, size
    initial = sum(w * inv.expected(n, size) for w, inv in zip(weights, invs))
    value = initial
    selected, trace = [], []
    for i in range(n):
        branches = {}
        for include in (False, True):
            q = quota - int(include)
            if 0 <= q <= remaining - 1:
                branches[include] = sum(w * inv.branch_expected(labels[i], remaining - 1, q, include)
                                       for w, inv, (_, labels, _) in zip(weights, invs, models))
        choose = max(branches, key=lambda k: (branches[k], k))
        previous = value
        if len(branches) == 2:
            assert previous == ((1 - Fraction(quota, remaining)) * branches[False]
                                + Fraction(quota, remaining) * branches[True])
        for inv, (_, labels, _) in zip(invs, models):
            inv.apply(labels[i], inv.branch_coefficients(choose))
        remaining -= 1
        quota -= int(choose)
        if choose:
            selected.append(i)
        value = sum(w * inv.expected(remaining, quota) for w, inv in zip(weights, invs))
        assert value == branches[choose] and value >= previous
        trace.append({"index": i, "include": choose, "objective": str(value),
                      "remaining": remaining, "quota": quota})
    assert len(selected) == size
    return {"selected_indices": selected, "initial_objective": initial,
            "final_objective": value, "trace": trace}


def cyclic_graph_models(modulus: int, domain: Sequence[int], values: Sequence[int],
                        eta: Scalar) -> list:
    if len(domain) != len(values):
        raise ValueError("domain and value lengths differ")
    if modulus < 1 or len({x % modulus for x in domain}) != len(domain):
        raise ValueError("domain must consist of distinct residues")
    eta = rational(eta)
    if not 0 < eta <= 1:
        raise ValueError("eta must be in (0,1]")
    return [(FiniteAbelianGroup((modulus,)), [(x % modulus,) for x in domain], -(1 - eta)),
            (FiniteAbelianGroup((modulus, modulus)),
             [(x % modulus, y % modulus) for x, y in zip(domain, values)], 1)]


def _jsonable(obj):
    if isinstance(obj, Fraction):
        return str(obj)
    if isinstance(obj, dict):
        return {k: _jsonable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)):
        return [_jsonable(x) for x in obj]
    return obj


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON cyclic-graph input")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    models = cyclic_graph_models(data["modulus"], data["domain"], data["values"], data["eta"])
    if "size" in data:
        result = fixed_size_round(models, data["order"], data["size"])
    else:
        result = deterministic_round(models, data["probabilities"], data["order"])
    result["selected_domain"] = [data["domain"][i] for i in result["selected_indices"]]
    text = json.dumps(_jsonable(result), indent=2)
    if args.output:
        args.output.write_text(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
