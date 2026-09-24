#!/usr/bin/env python3
"""Exact ordinal order-map calculations, using hereditary Cantor normal forms.

The mathematics applies to every ordinal. This executable represents ordinals
below epsilon_0, with finite hereditary Cantor normal forms. No third-party
packages are required. Run --demo, or pass a JSON input file (see README).
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from functools import total_ordering
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    """Canonical finite tuple of (exponent, positive coefficient), descending."""
    terms: tuple[tuple['Ordinal', int], ...] = ()

    def __post_init__(self) -> None:
        previous: Ordinal | None = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError('An exponent must be an Ordinal.')
            if type(coefficient) is not int or coefficient <= 0:
                raise ValueError('Cantor coefficients must be positive integers.')
            if previous is not None and not exponent < previous:
                raise ValueError('Cantor exponents must be strictly decreasing.')
            previous = exponent

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        for (a, ac), (b, bc) in zip(self.terms, other.terms):
            if a != b:
                return a < b
            if ac != bc:
                return ac < bc
        return len(self.terms) < len(other.terms)

    def __bool__(self) -> bool:
        return bool(self.terms)

    @classmethod
    def finite(cls, value: int) -> 'Ordinal':
        if type(value) is not int or value < 0:
            raise ValueError('A finite ordinal must be a nonnegative integer.')
        return cls(()) if value == 0 else cls(((cls(()), value),))

    @classmethod
    def collect(cls, terms: Iterable[tuple['Ordinal', int]]) -> 'Ordinal':
        coefficients: dict[Ordinal, int] = {}
        for exponent, coefficient in terms:
            if not isinstance(exponent, Ordinal) or type(coefficient) is not int:
                raise TypeError('Invalid Cantor term.')
            if coefficient < 0:
                raise ValueError('Negative coefficients are not allowed.')
            coefficients[exponent] = coefficients.get(exponent, 0) + coefficient
        return cls(tuple((e, coefficients[e]) for e in sorted(coefficients, reverse=True)
                         if coefficients[e]))

    def natural_sum(self, other: 'Ordinal') -> 'Ordinal':
        return Ordinal.collect(self.terms + other.terms)

    def natural_times(self, copies: int) -> 'Ordinal':
        if type(copies) is not int or copies < 0:
            raise ValueError('The number of copies must be a nonnegative integer.')
        return Ordinal.collect((e, c * copies) for e, c in self.terms)

    def natural_product(self, other: 'Ordinal') -> 'Ordinal':
        return Ordinal.collect((e.natural_sum(f), c*d)
                               for e, c in self.terms for f, d in other.terms)

    def ordinary_sum(self, other: 'Ordinal') -> 'Ordinal':
        if not other:
            return self
        exponent, coefficient = other.terms[0]
        prefix: list[tuple[Ordinal, int]] = []
        for e, c in self.terms:
            if e > exponent:
                prefix.append((e, c))
            elif e == exponent:
                coefficient += c
                break
            else:
                break
        return Ordinal(tuple(prefix + [(exponent, coefficient)] + list(other.terms[1:])))

    def predecessor(self) -> 'Ordinal':
        if not self.terms or self.terms[-1][0] != ZERO:
            raise ValueError('Only a nonzero successor ordinal has a predecessor.')
        e, c = self.terms[-1]
        return Ordinal(self.terms[:-1] + (((e, c-1),) if c > 1 else ()))

    def expand_exponents(self, max_blocks: int = 10000) -> tuple['Ordinal', ...]:
        count = sum(c for _, c in self.terms)
        if count > max_blocks:
            raise ValueError(f'{count} blocks exceeds the safety limit {max_blocks}.')
        return tuple(e for e, c in self.terms for _ in range(c))

    def to_json(self) -> Any:
        if not self:
            return 0
        if len(self.terms) == 1 and self.terms[0][0] == ZERO:
            return self.terms[0][1]
        return {'cnf': [[e.to_json(), c] for e, c in self.terms]}

    @classmethod
    def from_json(cls, value: Any) -> 'Ordinal':
        if type(value) is int:
            return cls.finite(value)
        if not isinstance(value, dict) or set(value) != {'cnf'}:
            raise ValueError('Use a nonnegative integer or {"cnf": [[exponent, coefficient], ...]}.')
        raw = value['cnf']
        if not isinstance(raw, list):
            raise ValueError('cnf must be a list.')
        terms = []
        for term in raw:
            if not isinstance(term, list) or len(term) != 2:
                raise ValueError('Each Cantor term must be [exponent, coefficient].')
            terms.append((cls.from_json(term[0]), term[1]))
        return cls(tuple(terms))  # Deliberately rejects unsorted/noncanonical input.

    def __str__(self) -> str:
        if not self:
            return '0'
        result = []
        for e, c in self.terms:
            if not e:
                result.append(str(c))
            else:
                base = 'omega' if e == ONE else f'omega^({e})'
                result.append(base if c == 1 else f'{base}*{c}')
        return ' + '.join(result)


ZERO = Ordinal()
ONE = Ordinal.finite(1)
OMEGA = Ordinal(((ONE, 1),))


def omega_power(exponent: Ordinal) -> Ordinal:
    return Ordinal(((exponent, 1),))


def natural_sum(values: Iterable[Ordinal]) -> Ordinal:
    result = ZERO
    for value in values:
        result = result.natural_sum(value)
    return result


@dataclass(frozen=True)
class Poset:
    n: int
    successors: tuple[int, ...]  # strict, transitively closed successor bitsets

    def __post_init__(self) -> None:
        if type(self.n) is not int or self.n < 0 or len(self.successors) != self.n:
            raise ValueError('Invalid size or relation length.')
        full = (1 << self.n) - 1
        for i, mask in enumerate(self.successors):
            if type(mask) is not int or mask < 0 or mask & ~full or mask & (1 << i):
                raise ValueError('Invalid strict order relation.')
            for j in range(self.n):
                if mask & (1 << j) and self.successors[j] & ~mask:
                    raise ValueError('Relation is not transitive.')

    @classmethod
    def from_edges(cls, n: int, edges: Iterable[Sequence[int]]) -> 'Poset':
        if type(n) is not int or n < 0:
            raise ValueError('n must be a nonnegative integer.')
        rows = [0] * n
        for pair in edges:
            if len(pair) != 2:
                raise ValueError('An edge must have two endpoints.')
            a, b = pair
            if type(a) is not int or type(b) is not int or not (0 <= a < n and 0 <= b < n):
                raise ValueError('Edge endpoint out of range.')
            rows[a] |= 1 << b
        for k in range(n):
            for i in range(n):
                if rows[i] & (1 << k):
                    rows[i] |= rows[k]
        if any(rows[i] & (1 << i) for i in range(n)):
            raise ValueError('The supplied edges contain a directed cycle.')
        return cls(n, tuple(rows))

    def edges(self) -> tuple[tuple[int, int], ...]:
        return tuple((i, j) for i in range(self.n) for j in range(self.n)
                     if self.successors[i] & (1 << j))

    def dual(self) -> 'Poset':
        rows = [0] * self.n
        for i, j in self.edges():
            rows[j] |= 1 << i
        return Poset(self.n, tuple(rows))

    def ideals(self) -> tuple[int, ...]:
        predecessors = self.dual().successors
        return tuple(mask for mask in range(1 << self.n)
                     if all(not (mask & (1 << i)) or not (predecessors[i] & ~mask)
                            for i in range(self.n)))

    def maps(self, colours: int) -> Iterator[tuple[int, ...]]:
        if type(colours) is not int or colours < 0:
            raise ValueError('The number of colours must be nonnegative.')
        edges = self.edges()
        for assignment in product(range(colours), repeat=self.n):
            if all(assignment[i] <= assignment[j] for i, j in edges):
                yield assignment

    def ideal_polynomial(self) -> list[int]:
        result = [0] * (self.n + 1)
        for mask in self.ideals():
            result[mask.bit_count()] += 1
        return result

    def filter_polynomial(self) -> list[int]:
        return self.dual().ideal_polynomial()


def order_map_type_direct(poset: Poset, beta: Ordinal,
                          assignment_limit: int = 2_000_000) -> Ordinal:
    """The finite Cantor-block formula, direct independent implementation."""
    exponents = beta.expand_exponents()
    if len(exponents) ** poset.n > assignment_limit:
        raise ValueError('Too many assignments for direct enumeration; use the DP.')
    result = ZERO
    for assignment in poset.maps(len(exponents)):
        result = result.natural_sum(omega_power(natural_sum(exponents[j] for j in assignment)))
    return result


def order_map_type(poset: Poset, beta: Ordinal, size_limit: int = 18) -> Ordinal:
    """Ideal-chain dynamic program for o(Mon(poset, beta)).

    A state I records the ideal filled by all blocks already processed.
    Its weight is an ordinal polynomial under natural sum and product.
    """
    if poset.n > size_limit:
        raise ValueError(f'n={poset.n} exceeds exponential-DP safety limit {size_limit}.')
    ideals = poset.ideals()
    extensions = {i: tuple(j for j in ideals if i & ~j == 0) for i in ideals}
    states = {0: ONE}
    for exponent in beta.expand_exponents():
        updated: dict[int, Ordinal] = {}
        factors = [omega_power(exponent.natural_times(k)) for k in range(poset.n + 1)]
        for i, value in states.items():
            for j in extensions[i]:
                term = value.natural_product(factors[(j ^ i).bit_count()])
                updated[j] = updated.get(j, ZERO).natural_sum(term)
        states = updated
    return states.get((1 << poset.n) - 1, ZERO)


def order_map_height(n: int, beta: Ordinal) -> Ordinal:
    """Exact height; depends on n but not on the relations of the finite poset."""
    if type(n) is not int or n < 0:
        raise ValueError('n must be a nonnegative integer.')
    if n == 0:
        return ONE
    if not beta:
        return ZERO
    delta, coefficient = beta.terms[-1]
    if not delta:
        return beta.predecessor().natural_times(n).ordinary_sum(ONE)
    rho = Ordinal(beta.terms[:-1] + (((delta, coefficient-1),) if coefficient > 1 else ()))
    return rho.natural_times(n).ordinary_sum(omega_power(delta))


def grid_powerset_type(poset: Poset, alpha: Ordinal) -> Ordinal:
    """o(P_f(alpha x poset)), including the empty subset and Hoare quotient."""
    return order_map_type(poset.dual(), ONE.ordinary_sum(alpha))


def grid_powerset_height(poset: Poset, alpha: Ordinal) -> Ordinal:
    return order_map_height(poset.n, ONE.ordinary_sum(alpha))


def examples() -> dict[str, Any]:
    fork = Poset.from_edges(3, [(0, 1), (0, 2)])
    dual = fork.dual()
    chain = Poset.from_edges(3, [(0, 1), (1, 2)])
    antichain = Poset.from_edges(3, [])
    alpha = OMEGA.ordinary_sum(ONE)
    result: dict[str, Any] = {}
    for name, poset in [('fork', fork), ('dual_fork', dual),
                        ('chain_3', chain), ('antichain_3', antichain)]:
        result[name] = {
            'strict_relations': poset.edges(),
            'filter_counts_by_size': poset.filter_polynomial(),
            'finite_order_map_counts_1_to_5': [sum(1 for _ in poset.maps(k)) for k in range(1, 6)],
            'grid_alpha': str(alpha),
            'powerset_maximal_order_type': str(grid_powerset_type(poset, alpha)),
            'powerset_height': str(grid_powerset_height(poset, alpha))}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path, help='JSON input file')
    parser.add_argument('--demo', action='store_true', help='Print the article examples')
    parser.add_argument('--output', type=Path, help='Write JSON to this file instead of stdout')
    args = parser.parse_args()
    try:
        if args.demo:
            result: Any = examples()
        elif args.input:
            raw = json.loads(args.input.read_text(encoding='utf-8'))
            poset = Poset.from_edges(raw['n'], raw.get('edges', []))
            ordinal = Ordinal.from_json(raw['ordinal'])
            mode = raw.get('mode', 'grid')
            if mode == 'grid':
                value = grid_powerset_type(poset, ordinal)
                height = grid_powerset_height(poset, ordinal)
            elif mode == 'maps':
                value = order_map_type(poset, ordinal)
                height = order_map_height(poset.n, ordinal)
            else:
                raise ValueError('mode must be "grid" or "maps".')
            result = {'maximal_order_type': str(value), 'height': str(height),
                      'maximal_order_type_cnf': value.to_json(), 'height_cnf': height.to_json()}
        else:
            parser.error('Specify --demo or a JSON input file.')
        text = json.dumps(result, indent=2) + '\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
        else:
            print(text, end='')
    except (ValueError, TypeError, KeyError, OSError, json.JSONDecodeError) as exc:
        parser.exit(2, f'error: {exc}\n')


if __name__ == '__main__':
    main()
