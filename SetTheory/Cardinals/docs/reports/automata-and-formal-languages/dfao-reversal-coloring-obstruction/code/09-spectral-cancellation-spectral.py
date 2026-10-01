#!/usr/bin/env python3
"""Exact spectral formulas for the explicit binary-DFAO witness deficit.

No computation of unknown optimum values is performed.  All integer
polynomials are represented in ascending coefficient order.  Python >= 3.10;
standard library only.  See article.tex for the proofs and transfer hypotheses.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from math import comb, isqrt
from typing import Iterable

Poly = list[int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def multiply(a: Poly, b: Poly) -> Poly:
    """Multiply integer polynomials, ascending coefficients."""
    result = [0] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            result[i + j] += u * v
    return result


def polynomial(factors: Iterable[Poly]) -> Poly:
    answer = [1]
    for factor in factors:
        answer = multiply(answer, factor)
    return answer


@dataclass(frozen=True)
class Moment:
    product: int
    T: int
    U: int
    V: int
    # Ordered factor pairs, with one signed multinomial coefficient each.
    pairs: tuple[tuple[int, int, int], ...]

    @property
    def W(self) -> int:
        return self.product * self.U + self.V

    @property
    def Z(self) -> int:
        return self.product * self.U - self.V

    @property
    def off_diagonal(self) -> bool:
        return any(r != s for r, s, _ in self.pairs)

    def factors(self) -> list[Poly]:
        """Exact rational factors for the four full-sequence modes."""
        p = self.product
        root = isqrt(p)
        factors: list[Poly] = []
        if root * root == p:
            if self.W + 2 * root**3 * self.T != 0:
                factors.append([-root, 1])
            if self.W - 2 * root**3 * self.T != 0:
                factors.append([root, 1])
        elif self.W != 0 or self.T != 0:
            factors.append([-p, 0, 1])
        if self.Z != 0:
            factors.append([p, 0, 1])
        return factors

    def residue_coefficient(self, residue: int) -> Fraction:
        require(residue in range(4), "residue must be 0, 1, 2, or 3")
        return (Fraction(self.U, self.product), Fraction(self.T),
                Fraction(self.V, self.product),
                Fraction(self.product * self.T))[residue]


def moments(k: int) -> dict[int, Moment]:
    require(isinstance(k, int) and k >= 3, "k must be an integer >= 3")
    accum: dict[int, list[int]] = defaultdict(lambda: [0, 0, 0])
    pairs: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    for r in range(1, k):
        for s in range(1, k - r + 1):
            c = (-1)**(k - r - s) * comb(k, r) * comb(k - r, s)
            p = r * s
            accum[p][0] += c * s
            accum[p][1] += c * s**2
            accum[p][2] += c * s**4
            pairs[p].append((r, s, c))
    return {p: Moment(p, *accum[p], tuple(pairs[p])) for p in sorted(accum)}


def full_factors(k: int, data: dict[int, Moment] | None = None) -> list[Poly]:
    """Minimal factors for D*_k(n), including the polynomial/periodic part."""
    if data is None:
        data = moments(k)
    unit_multiplicity = 2 if k == 3 else 3
    factors = [[-1, 1] for _ in range(unit_multiplicity)]
    factors += [[1, 1], [1, 0, 1]]
    for p, m in data.items():
        if p != 1:
            factors.extend(m.factors())
    return factors


def residue_factors(k: int, residue: int,
                    data: dict[int, Moment] | None = None) -> list[Poly]:
    if data is None:
        data = moments(k)
    require(residue in range(4), "residue must be between 0 and 3")
    factors = [[-1, 1] for _ in range(2 if k == 3 else 3)]
    for p, m in data.items():
        if p != 1 and m.residue_coefficient(residue) != 0:
            factors.append([-p * p, 1])
    return factors


def split(n: int) -> tuple[int, int]:
    require(isinstance(n, int) and n >= 7, "n must be an integer >= 7")
    h = n // 2
    if n % 2:
        return h, h + 1
    displacement = 1 if n % 4 == 0 else 2
    return h - displacement, h + displacement


def onto_table(max_a: int, k: int, modulus: int | None = None) -> list[list[int]]:
    """Surjections onto i labeled colors: i! S(a,i), by positive recurrence."""
    table = [[0] * (k + 1) for _ in range(max_a + 1)]
    table[0][0] = 1
    for a in range(1, max_a + 1):
        for i in range(1, min(a, k) + 1):
            value = i * (table[a - 1][i] + table[a - 1][i - 1])
            table[a][i] = value if modulus is None else value % modulus
    return table


def positive_coloring(k: int, a: int, b: int,
                      table: list[list[int]] | None = None,
                      modulus: int | None = None) -> int:
    require(k >= 1 and a >= 1 and b >= 1, "positive k, a, b are required")
    if table is None:
        table = onto_table(a, k, modulus)
    total = 0
    for i in range(1, min(a, k - 1) + 1):
        power = (k - i)**b if modulus is None else pow(k - i, b, modulus)
        total += comb(k, i) * table[a][i] * power
    return total if modulus is None else total % modulus


def signed_coloring(k: int, a: int, b: int) -> int:
    return sum((-1)**(k-r-s) * comb(k, r) * comb(k-r, s) * r**a * s**b
               for r in range(1, k) for s in range(1, k-r+1))


def witness_values(k: int, indices: list[int],
                   modulus: int | None = None) -> list[int]:
    """Evaluate via the positive Stirling formula, independently of moments."""
    require(k >= 3 and all(n >= 7 for n in indices), "invalid k or index")
    if not indices:
        return []
    pairs = [split(n) for n in indices]
    table = onto_table(max(a for a, _ in pairs), k, modulus)
    values = []
    for a, b in pairs:
        value = positive_coloring(k, a, b, table, modulus)
        value -= b if k == 3 else a * b
        values.append(value if modulus is None else value % modulus)
    return values


def tail_numerator(k: int, start: int = 7) -> tuple[Poly, Poly]:
    """Return numerator, reduced denominator for sum D*(start+n) z**n."""
    q = polynomial(full_factors(k))
    denominator = q[::-1]
    d = len(q) - 1
    values = witness_values(k, list(range(start, start + d)))
    numerator = [sum(denominator[j] * values[i-j] for j in range(i+1))
                 for i in range(d)]
    while len(numerator) > 1 and numerator[-1] == 0:
        numerator.pop()
    return numerator, denominator


if __name__ == "__main__":
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k", type=int)
    parser.add_argument("--expanded", action="store_true")
    args = parser.parse_args()
    data = moments(args.k)
    factors = full_factors(args.k, data)
    answer = {
        "k": args.k,
        "sequence": "explicit witness deficit, not independently computed optimum",
        "product_count": len(data),
        "full_factors_ascending": factors,
        "full_order": sum(len(f)-1 for f in factors),
        "residue_orders": [sum(len(f)-1 for f in residue_factors(args.k, r, data))
                           for r in range(4)],
    }
    if args.expanded:
        answer["full_polynomial_ascending"] = polynomial(factors)
    print(json.dumps(answer, indent=2))
