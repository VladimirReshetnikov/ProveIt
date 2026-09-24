"""Finite-poset frontier calculations for the accompanying research article.

All vertex labels are integers 0,...,n-1.  An edge (i,j) means i < j.
The constructor accepts a Hasse diagram or any acyclic set of generating edges.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from typing import Iterable, Iterator
from ordinals import Ordinal, ZERO, ONE, OMEGA, natural_sum


def bits(mask: int) -> Iterator[int]:
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


@dataclass(frozen=True)
class FinitePoset:
    successors: tuple[int, ...]  # strict transitive closure

    def __post_init__(self):
        n = len(self.successors)
        limit = (1 << n) - 1
        for i, row in enumerate(self.successors):
            if type(row) is not int or row < 0 or row & ~limit or row & (1 << i):
                raise ValueError('Invalid strict-order bit mask.')
            for j in bits(row):
                if self.successors[j] & ~row:
                    raise ValueError('The relation is not transitive.')

    @classmethod
    def from_edges(cls, n: int, edges: Iterable[tuple[int, int]]) -> 'FinitePoset':
        if type(n) is not int or n < 0:
            raise ValueError('n must be a nonnegative integer.')
        rows = [0] * n
        for i, j in edges:
            if not (0 <= i < n and 0 <= j < n):
                raise ValueError('Edge endpoint out of range.')
            rows[i] |= 1 << j
        for k in range(n):
            for i in range(n):
                if rows[i] & (1 << k):
                    rows[i] |= rows[k]
        return cls(tuple(rows))

    @property
    def n(self) -> int:
        return len(self.successors)

    @property
    def predecessors(self) -> tuple[int, ...]:
        return tuple(sum(1 << i for i, row in enumerate(self.successors)
                         if row & (1 << j)) for j in range(self.n))

    def is_antichain(self, mask: int) -> bool:
        return all(not (self.successors[i] & mask) for i in bits(mask))

    def antichains(self, maximal: bool = False) -> list[int]:
        predecessors = self.predecessors
        result = []
        for mask in range(1 << self.n):
            if not self.is_antichain(mask):
                continue
            if maximal:
                comparable = mask
                for i in bits(mask):
                    comparable |= self.successors[i] | predecessors[i]
                if comparable != (1 << self.n) - 1:
                    continue
            result.append(mask)
        return result

    def strict_downset(self, mask: int) -> int:
        predecessors = self.predecessors
        result = 0
        for i in bits(mask):
            result |= predecessors[i]
        return result

    def ideals(self) -> list[int]:
        predecessors = self.predecessors
        return [mask for mask in range(1 << self.n)
                if all(not (predecessors[i] & ~mask) for i in bits(mask))]

    def topological_order(self) -> list[int]:
        pred = self.predecessors
        remaining = (1 << self.n) - 1
        result = []
        while remaining:
            available = [i for i in bits(remaining) if not pred[i] & remaining]
            if not available:
                raise ValueError('Cycle detected.')
            i = min(available)
            result.append(i)
            remaining ^= 1 << i
        return result

    def height(self) -> int:
        length = [0] * self.n
        pred = self.predecessors
        for i in self.topological_order():
            length[i] = 1 + max((length[j] for j in bits(pred[i])), default=0)
        return max(length, default=0)

    def width(self) -> int:
        return max((a.bit_count() for a in self.antichains()), default=0)

    def frontier_poset(self) -> tuple[list[int], 'FinitePoset']:
        if not self.n:
            return [], FinitePoset(())
        antichains = self.antichains(maximal=True)
        downsets = [self.strict_downset(a) for a in antichains]
        rows = tuple(sum(1 << j for j, e in enumerate(downsets)
                         if d != e and not d & ~e) for d in downsets)
        return antichains, FinitePoset(rows)


def survivor_value(index: FinitePoset, exponents: list[Ordinal]):
    if len(exponents) != index.n:
        raise ValueError('One exponent is required for each stratum.')
    surviving = [i for i in range(index.n)
                 if not any(exponents[j] > exponents[i]
                            for j in bits(index.successors[i]))]
    value = natural_sum(Ordinal.omega_power(exponents[i]) for i in surviving)
    return value, surviving


def max_topological_sum(index: FinitePoset, exponents: list[Ordinal]) -> Ordinal:
    """Independent subset-DP oracle for the best WHOLE-STRATUM ordering.

    This is not a computation of an infinite bad-sequence tree.  Equality with
    the true maximal order type uses the article's cofinal-absorption proof.
    """
    if len(exponents) != index.n:
        raise ValueError('One exponent is required for each vertex.')
    if index.n > 24:
        raise ValueError('Subset DP deliberately limited to 24 vertices.')
    weights = [Ordinal.omega_power(e) for e in exponents]
    @lru_cache(None)
    def solve(mask: int) -> Ordinal:
        if not mask:
            return ZERO
        # Remove the last (therefore maximal) element of this induced subposet.
        return max(solve(mask ^ (1 << i)) + weights[i] for i in bits(mask)
                   if not index.successors[i] & mask)
    return solve((1 << index.n) - 1)


def powerset_max_type(q: FinitePoset, fiber_exponents: list[Ordinal]):
    """Assumes o(K(P_i))=omega**fiber_exponents[i] and no finite cofinal set."""
    if len(fiber_exponents) != q.n:
        raise ValueError('One fiber exponent is required for each vertex.')
    if any(not e for e in fiber_exponents):
        raise ValueError('The theorem requires strictly positive fiber exponents.')
    if not q.n:
        return ONE, [], [], FinitePoset(())
    antichains, index = q.frontier_poset()
    exponents = [natural_sum(fiber_exponents[i] for i in bits(a))
                 for a in antichains]
    value, surviving = survivor_value(index, exponents)
    return value, surviving, exponents, index


def uniform_invariants(q: FinitePoset, rho: Ordinal = ONE) -> dict:
    if not rho:
        raise ValueError('rho must be positive, so omega**rho is infinite.')
    if not q.n:
        return dict(max_type='1', height='1', coefficients={}, frontiers=[])
    antichains, index = q.frontier_poset()
    value, surviving, exponents, _ = powerset_max_type(q, [rho] * q.n)
    coefficients: dict[int, int] = {}
    for i in surviving:
        k = antichains[i].bit_count()
        coefficients[k] = coefficients.get(k, 0) + 1
    alpha = Ordinal.omega_power(rho)
    return {
        'max_type': str(value), 'max_type_cnf': value.to_json(),
        'height': str(alpha.times_finite(index.height())),
        'height_cnf': alpha.times_finite(index.height()).to_json(),
        'frontier_height': index.height(),
        'coefficients': dict(sorted(coefficients.items(), reverse=True)),
        'frontiers': [dict(vertices=list(bits(a)),
                           completed=list(bits(q.strict_downset(a))),
                           exponent=str(exponents[i]), surviving=i in surviving)
                      for i, a in enumerate(antichains)],
    }


def lex_sum_max_type(q: FinitePoset, fiber_types: list[Ordinal]) -> Ordinal:
    """Appendix formula. Zero fibers are permitted and are ignored."""
    if len(fiber_types) != q.n:
        raise ValueError('One type is required for each vertex.')
    contributions = []
    for i, value in enumerate(fiber_types):
        if not value:
            continue
        threshold = max((fiber_types[j].degree for j in bits(q.successors[i])
                         if fiber_types[j]), default=ZERO)
        contributions.append(value.truncate(threshold))
    return natural_sum(contributions)


def natural_posets(n: int) -> Iterator[FinitePoset]:
    """All posets with i<j whenever i <_Q j, without isomorphism reduction."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        rows = [0] * n
        for k in bits(mask):
            i, j = pairs[k]
            rows[i] |= 1 << j
        if all(not rows[j] & ~rows[i] for i in range(n) for j in bits(rows[i])):
            yield FinitePoset(tuple(rows))


def ideal_count_encoding(r: FinitePoset) -> FinitePoset:
    n = r.n
    return FinitePoset.from_edges(2*n,
        [(i, n+j) for i in range(n) for j in range(n)
         if i == j or r.successors[i] & (1 << j)])


EXAMPLES = {
    'chain_4': FinitePoset.from_edges(4, [(0, 1), (1, 2), (2, 3)]),
    'antichain_4': FinitePoset.from_edges(4, []),
    'two_levels_2_plus_2': FinitePoset.from_edges(4,
        [(0, 2), (0, 3), (1, 2), (1, 3)]),
    'N': FinitePoset.from_edges(4, [(0, 2), (1, 2), (1, 3)]),
    'two_disjoint_2_chains': FinitePoset.from_edges(4, [(0, 2), (1, 3)]),
    'V': FinitePoset.from_edges(3, [(0, 1), (0, 2)]),
    'inverted_V': FinitePoset.from_edges(3, [(0, 2), (1, 2)]),
    'isolated_point_plus_2_chain': FinitePoset.from_edges(3, [(1, 2)]),
}


if __name__ == '__main__':
    import json
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', help='JSON with n, edges, and optional rho')
    args = parser.parse_args()
    try:
        if args.input:
            with open(args.input, encoding='utf-8') as stream:
                specification = json.load(stream)
            q = FinitePoset.from_edges(specification['n'], specification.get('edges', []))
            modes = [key for key in ('rho', 'fiber_exponents', 'fiber_types')
                     if key in specification]
            if len(modes) > 1:
                raise ValueError('Specify only one of rho, fiber_exponents, fiber_types.')
            if 'fiber_exponents' in specification:
                weights = [Ordinal.from_json(v) for v in specification['fiber_exponents']]
                value, surviving, exponents, index = powerset_max_type(q, weights)
                antichains, _ = q.frontier_poset()
                output = {
                    'max_type': str(value), 'max_type_cnf': value.to_json(),
                    'scope': 'Maximal type of K(lexicographic sum); assumes '
                             'o(K(P_i))=omega**fiber_exponents[i]. '
                             'No nonuniform height formula is asserted.',
                    'frontiers': [dict(vertices=list(bits(a)),
                                       exponent=str(exponents[i]), surviving=i in surviving)
                                  for i,a in enumerate(antichains)]}
            elif 'fiber_types' in specification:
                types = [Ordinal.from_json(v) for v in specification['fiber_types']]
                value = lex_sum_max_type(q, types)
                output = {'max_type': str(value), 'max_type_cnf': value.to_json(),
                          'scope': 'Maximal type of the lexicographic sum itself, '
                                   'not of its finitary powerset.'}
            else:
                rho = Ordinal.from_json(specification.get('rho', 1))
                output = uniform_invariants(q, rho)
        else:
            output = {name: uniform_invariants(q) for name, q in EXAMPLES.items()}
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    print(json.dumps(output, indent=2))
