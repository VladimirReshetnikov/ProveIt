#!/usr/bin/env python3
"""Exact retirement-path heights for finite lexicographic sums of ordinal chains.

Standard-library only. Exponents in executable input are nonnegative integers;
fibre exponents must be positive. More generally these integers can be read as
ranks in any finite ordered list of positive ordinal exponents: the output has
the same coefficient pattern after order-preserving substitution.

This is an implementation of the accompanying theorem, not a proof assistant.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import product
import json
from pathlib import Path
from typing import Iterable, Iterator, Sequence


@dataclass(frozen=True, order=True)
class Ordinal:
    """Finite Cantor normal forms below omega**omega, as decreasing term pairs."""
    terms: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        previous: int | None = None
        for exponent, coefficient in self.terms:
            if (not isinstance(exponent, int) or isinstance(exponent, bool)
                    or not isinstance(coefficient, int) or isinstance(coefficient, bool)
                    or exponent < 0 or coefficient <= 0):
                raise ValueError("CNF terms require a nonnegative exponent and positive coefficient")
            if previous is not None and exponent >= previous:
                raise ValueError("CNF exponents must be strictly decreasing")
            previous = exponent

    @classmethod
    def mono(cls, exponent: int, coefficient: int = 1) -> Ordinal:
        return cls(((exponent, coefficient),))

    def __add__(self, other: Ordinal) -> Ordinal:
        if not isinstance(other, Ordinal):
            return NotImplemented
        if not other.terms:
            return self
        exponent, coefficient = other.terms[0]
        kept = tuple(term for term in self.terms if term[0] > exponent)
        equal = next((c for e, c in self.terms if e == exponent), 0)
        return Ordinal(kept + ((exponent, equal + coefficient),) + other.terms[1:])

    def natural_sum(self, other: Ordinal) -> Ordinal:
        coefficients = dict(self.terms)
        for exponent, coefficient in other.terms:
            coefficients[exponent] = coefficients.get(exponent, 0) + coefficient
        return Ordinal(tuple(sorted(coefficients.items(), reverse=True)))

    def successor(self) -> Ordinal:
        return self + Ordinal.mono(0)

    def relabel(self, labels: dict[int, int]) -> Ordinal:
        return Ordinal(tuple((labels[e], c) for e, c in self.terms))

    def to_json(self) -> list[list[int]]:
        return [list(term) for term in self.terms]

    def __str__(self) -> str:
        if not self.terms:
            return "0"
        parts = []
        for exponent, coefficient in self.terms:
            base = "1" if exponent == 0 else "omega" if exponent == 1 else f"omega^{exponent}"
            parts.append(str(coefficient) if exponent == 0 else
                         base if coefficient == 1 else f"{base}*{coefficient}")
        return " + ".join(parts)


ZERO = Ordinal()
ONE = Ordinal.mono(0)


def ordinal_sum(values: Iterable[Ordinal]) -> Ordinal:
    result = ZERO
    for value in values:
        result = result + value
    return result


def natural_sum(values: Iterable[Ordinal]) -> Ordinal:
    result = ZERO
    for value in values:
        result = result.natural_sum(value)
    return result


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


class Poset:
    """Finite labelled poset. Input may give Hasse edges or all strict pairs."""
    def __init__(self, n: int, edges: Iterable[Sequence[int]]) -> None:
        if not isinstance(n, int) or isinstance(n, bool) or n < 0:
            raise ValueError("n must be a nonnegative integer")
        self.n = n
        rows = [1 << i for i in range(n)]
        for edge in edges:
            if len(edge) != 2:
                raise ValueError("each edge must have two endpoints")
            a, b = edge
            if (not isinstance(a, int) or not isinstance(b, int)
                    or isinstance(a, bool) or isinstance(b, bool)
                    or not 0 <= a < n or not 0 <= b < n or a == b):
                raise ValueError("edge endpoints must be distinct vertex indices")
            rows[a] |= 1 << b
        for k in range(n):
            for i in range(n):
                if rows[i] & (1 << k):
                    rows[i] |= rows[k]
        if any(i != j and rows[i] >> j & 1 and rows[j] >> i & 1
               for i in range(n) for j in range(n)):
            raise ValueError("the supplied relation has a directed cycle")
        self.rows = tuple(rows)
        self.down = tuple(sum(1 << i for i in range(n) if rows[i] >> j & 1)
                          for j in range(n))
        self.comparable = tuple(rows[i] | self.down[i] for i in range(n))
        self.antichains = tuple(a for a in range(1 << n) if self.is_antichain(a))
        self.frontiers = tuple(a for a in self.antichains if self.is_maximal(a))
        self.frontier_pairs = tuple((a, b) for a in self.frontiers for b in self.frontiers
                                    if a != b and self.hoare(a, b))
        self.successors = {a: tuple(b for x, b in self.frontier_pairs if x == a)
                           for a in self.frontiers}
        self.covers = {a: tuple(b for b in self.successors[a]
                               if not any(c != b and self.hoare(c, b)
                                          for c in self.successors[a]))
                       for a in self.frontiers}
        # A strict Hoare comparison strictly increases the generated downset.
        self.topological = tuple(sorted(self.frontiers,
                                        key=lambda a: (self.downset(a).bit_count(), a)))

    def le(self, a: int, b: int) -> bool:
        return bool(self.rows[a] & (1 << b))

    def is_antichain(self, mask: int) -> bool:
        return all((mask & self.comparable[i]) == (1 << i) for i in bits(mask))

    def is_maximal(self, mask: int) -> bool:
        comparable = 0
        for i in bits(mask):
            comparable |= self.comparable[i]
        return comparable == (1 << self.n) - 1

    def hoare(self, a: int, b: int) -> bool:
        return all(self.rows[i] & b for i in bits(a))

    def downset(self, mask: int) -> int:
        result = 0
        for i in bits(mask):
            result |= self.down[i]
        return result

    def complete(self, a: int) -> int:
        if a not in self.antichains:
            raise ValueError("completion requires an antichain")
        incomparable = ((1 << self.n) - 1)
        for i in bits(a):
            incomparable &= ~self.comparable[i]
        minima = sum(1 << i for i in bits(incomparable)
                     if self.down[i] & incomparable == 1 << i)
        return a | minima

    def strict_edges(self) -> list[list[int]]:
        return [[i, j] for i in range(self.n) for j in range(self.n)
                if i != j and self.le(i, j)]

    def chains(self) -> tuple[tuple[int, ...], ...]:
        """All nonempty strict frontier chains; independent brute-force oracle."""
        result: list[tuple[int, ...]] = []
        def visit(chain: tuple[int, ...]) -> None:
            result.append(chain)
            for b in self.successors[chain[-1]]:
                visit(chain + (b,))
        for a in self.frontiers:
            visit((a,))
        return tuple(result)


def validate_exponents(poset: Poset, exponents: Sequence[int]) -> None:
    if len(exponents) != poset.n:
        raise ValueError("one positive fibre exponent is required for each vertex")
    if any(not isinstance(e, int) or isinstance(e, bool) or e <= 0 for e in exponents):
        raise ValueError("fibre exponents must be positive integers")


def maximum_weight(mask: int, exponents: Sequence[int]) -> Ordinal:
    if mask == 0:
        raise ValueError("a retirement group must be nonempty")
    return Ordinal.mono(max(exponents[i] for i in bits(mask)))


def path_cost(path: Sequence[int], exponents: Sequence[int]) -> Ordinal:
    if not path:
        raise ValueError("a path must be nonempty")
    return ordinal_sum([maximum_weight(a & ~b, exponents)
                        for a, b in zip(path, path[1:])]
                       + [maximum_weight(path[-1], exponents)])


def height(poset: Poset, exponents: Sequence[int], *, cover_only: bool = False
           ) -> tuple[Ordinal, tuple[int, ...]]:
    """Return exact height and a maximizing frontier chain certificate."""
    validate_exponents(poset, exponents)
    if poset.n == 0:
        return ONE, ()  # K(empty) has exactly the empty downset.
    nexts = poset.covers if cover_only else poset.successors
    values: dict[int, Ordinal] = {}
    paths: dict[int, tuple[int, ...]] = {}
    for a in reversed(poset.topological):
        best = maximum_weight(a, exponents)
        path = (a,)
        for b in nexts[a]:
            candidate = maximum_weight(a & ~b, exponents) + values[b]
            candidate_path = (a,) + paths[b]
            # On ties, prefer longer paths for more informative certificates.
            if candidate > best or (candidate == best and len(candidate_path) > len(path)):
                best, path = candidate, candidate_path
        values[a], paths[a] = best, path
    start = poset.complete(0)
    return values[start], paths[start]


def certificate(poset: Poset, exponents: Sequence[int]) -> dict:
    value, path = height(poset, exponents, cover_only=True)
    groups = [a & ~b for a, b in zip(path, path[1:])]
    if path:
        groups.append(path[-1])
    return {
        "n": poset.n,
        "edges": poset.strict_edges(),
        "exponents": list(exponents),
        "height_cnf": value.to_json(),
        "height_display": str(value),
        "frontiers": [list(bits(a)) for a in poset.frontiers],
        "maximizing_path": [list(bits(a)) for a in path],
        "retirement_groups_including_terminal": [list(bits(a)) for a in groups],
        "weights": [str(maximum_weight(a, exponents)) for a in groups],
        "pivot_vertices": [max(bits(a), key=lambda q: (exponents[q], -q)) for a in groups],
    }


def expand_limit_fibres(poset: Poset, fibres: Sequence[Ordinal]
                        ) -> tuple[Poset, tuple[int, ...], tuple[int, ...]]:
    """Expand nonzero limit CNFs into monomial blocks; return owner map too."""
    if len(fibres) != poset.n:
        raise ValueError("one CNF fibre is required per vertex")
    exponents: list[int] = []
    owners: list[int] = []
    for q, fibre in enumerate(fibres):
        if not fibre.terms or fibre.terms[-1][0] == 0:
            raise ValueError("each fibre must be a nonzero limit ordinal (no finite tail)")
        for exponent, coefficient in fibre.terms:
            exponents.extend([exponent] * coefficient)
            owners.extend([q] * coefficient)
    edges = []
    for i, q in enumerate(owners):
        for j, r in enumerate(owners):
            if (q == r and i < j) or (q != r and poset.le(q, r)):
                edges.append((i, j))
    return Poset(len(owners), edges), tuple(exponents), tuple(owners)


def from_json(data: dict) -> dict:
    if not isinstance(data, dict):
        raise ValueError("input must be a JSON object")
    poset = Poset(data["n"], data.get("edges", []))
    if "exponents" in data and "fibres_cnf" in data:
        raise ValueError("choose exponents or fibres_cnf, not both")
    if "fibres_cnf" in data:
        fibres = [Ordinal(tuple(tuple(term) for term in cnf)) for cnf in data["fibres_cnf"]]
        expanded, exponents, owners = expand_limit_fibres(poset, fibres)
        result = certificate(expanded, exponents)
        result["expanded_from_original_vertices"] = list(owners)
        result["original_fibres_cnf"] = data["fibres_cnf"]
        return result
    return certificate(poset, data.get("exponents", [1] * poset.n))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON finite-poset and fibre specification")
    parser.add_argument("--output", type=Path, help="write JSON certificate to this file")
    args = parser.parse_args()
    try:
        result = from_json(json.loads(args.input.read_text(encoding="utf-8")))
    except (OSError, ValueError, TypeError, KeyError) as error:
        parser.exit(2, f"error: {error}\n")
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
