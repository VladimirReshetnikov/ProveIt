"""Exact heights of finitary powersets of finite ordinal lexicographic sums.

Run: python code/heights.py examples/weighted_N.json
See article.tex for the transfinite proof. This program checks finite symbolic
certificates; it does not formally verify that proof.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator
from ordinals import Ordinal, ZERO, ONE, ordinal_sum


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Poset:
    n: int
    pred: tuple[int, ...]
    succ: tuple[int, ...]

    @staticmethod
    def from_edges(n: int, edges: list[list[int]] | list[tuple[int, int]]) -> 'Poset':
        if type(n) is not int or n < 0:
            raise ValueError('n must be a nonnegative integer')
        succ = [0] * n
        for edge in edges:
            if len(edge) != 2 or any(type(v) is not int or not 0 <= v < n for v in edge):
                raise ValueError('Each edge must contain two valid vertex indices')
            u, v = edge
            succ[u] |= 1 << v
        for k in range(n):
            for i in range(n):
                if succ[i] >> k & 1:
                    succ[i] |= succ[k]
        if any(succ[i] >> i & 1 for i in range(n)):
            raise ValueError('Strict order contains a directed cycle')
        pred = [0] * n
        for i in range(n):
            for j in bits(succ[i]):
                pred[j] |= 1 << i
        return Poset(n, tuple(pred), tuple(succ))

    def is_ideal(self, mask: int) -> bool:
        return all(self.pred[v] & ~mask == 0 for v in bits(mask))

    def ideals(self) -> list[int]:
        return [m for m in range(1 << self.n) if self.is_ideal(m)]

    def maxima(self, mask: int) -> int:
        return sum(1 << v for v in bits(mask) if not self.succ[v] & mask)

    def available(self, mask: int) -> list[int]:
        return [v for v in range(self.n)
                if not mask >> v & 1 and self.pred[v] & ~mask == 0]

    def downclosure(self, mask: int) -> int:
        result = mask
        for v in bits(mask):
            result |= self.pred[v]
        return result

    def maximal_antichains(self) -> list[int]:
        answer = []
        for mask in range(1 << self.n):
            if any(self.succ[v] & mask for v in bits(mask)):
                continue
            comparable = mask
            for v in bits(mask):
                comparable |= self.pred[v] | self.succ[v]
            if comparable == (1 << self.n) - 1:
                answer.append(mask)
        return answer


def retirement_weight(poset: Poset, weights: list[Ordinal], ideal: int, v: int) -> Ordinal:
    retired = poset.maxima(ideal) & poset.pred[v]
    return max([ONE] + [weights[a] for a in bits(retired)])


def pure_height(poset: Poset, weights: list[Ordinal]) -> tuple[Ordinal, dict[str, Any]]:
    if len(weights) != poset.n or any(not w.is_pure for w in weights):
        raise ValueError('There must be one pure nonzero weight per vertex')
    full = (1 << poset.n) - 1
    values: dict[int, Ordinal] = {0: ZERO}
    previous: dict[int, tuple[int, int]] = {}
    edge_count = 0
    for ideal in range(1 << poset.n):
        if ideal not in values:
            continue
        for v in poset.available(ideal):
            edge_count += 1
            new = ideal | 1 << v
            candidate = values[ideal] + retirement_weight(poset, weights, ideal, v)
            if new not in values or values[new] < candidate:
                values[new] = candidate
                previous[new] = (ideal, v)
    terminal = max([ONE] + [weights[a] for a in bits(poset.maxima(full))])
    height = values[full] + terminal
    path = []
    cursor = full
    while cursor:
        old, v = previous[cursor]
        retired = poset.maxima(old) & poset.pred[v]
        path.append({'vertex': v, 'before': old, 'after': cursor,
                     'retired': list(bits(retired)),
                     'cost': retirement_weight(poset, weights, old, v).to_json()})
        cursor = old
    path.reverse()
    certificate = {
        'height': height.to_json(), 'height_text': str(height),
        'vertices': poset.n, 'ideal_count': len(values), 'edge_count': edge_count,
        'strict_edges': [[i, j] for i in range(poset.n) for j in bits(poset.succ[i])],
        'weights': [w.to_json() for w in weights],
        'values': {str(k): v.to_json() for k, v in sorted(values.items())},
        'winning_path': path, 'terminal': terminal.to_json()
    }
    return height, certificate


def check_certificate(certificate: dict[str, Any]) -> bool:
    """Recheck every ideal recurrence and independently sum the witness path."""
    p = Poset.from_edges(certificate['vertices'], certificate['strict_edges'])
    w = [Ordinal.from_json(x) for x in certificate['weights']]
    if len(w) != p.n or any(not x.is_pure for x in w):
        return False
    if 'source_input' in certificate:
        data = certificate['source_input']
        original = Poset.from_edges(data['n'], data.get('edges', []))
        fibers = [Ordinal.from_json(x) for x in data['fiber_types']]
        rebuilt, rebuilt_weights, rebuilt_blocks = expand(original, fibers, p.n)
        if (rebuilt != p or rebuilt_weights != w
                or certificate.get('blocks') != rebuilt_blocks):
            return False
    values = {int(k): Ordinal.from_json(v) for k, v in certificate['values'].items()}
    ideals = p.ideals()
    if set(values) != set(ideals) or values.get(0) != ZERO:
        return False
    for ideal in ideals:
        if not ideal:
            continue
        candidates = []
        for v in bits(p.maxima(ideal)):
            before = ideal ^ (1 << v)
            candidates.append(values[before] + retirement_weight(p, w, before, v))
        if values[ideal] != max(candidates):
            return False
    current, score = 0, ZERO
    for step in certificate['winning_path']:
        v = step['vertex']
        if step['before'] != current or v not in p.available(current):
            return False
        cost = retirement_weight(p, w, current, v)
        if step['retired'] != list(bits(p.maxima(current) & p.pred[v])):
            return False
        if Ordinal.from_json(step['cost']) != cost:
            return False
        score = score + cost
        current |= 1 << v
        if step['after'] != current:
            return False
    full = (1 << p.n) - 1
    terminal = max([ONE] + [w[a] for a in bits(p.maxima(full))])
    claimed = Ordinal.from_json(certificate['height'])
    return (current == full and Ordinal.from_json(certificate['terminal']) == terminal
            and score + terminal == values[full] + terminal == claimed)


def expand(poset: Poset, fibers: list[Ordinal], max_vertices: int = 20
           ) -> tuple[Poset, list[Ordinal], list[dict[str, Any]]]:
    if len(fibers) != poset.n:
        raise ValueError('fiber_types length must equal n')
    total = sum(c for x in fibers for _, c in x.terms)
    if total > max_vertices:
        raise ValueError(f'CNF expansion has {total} vertices; safety limit is {max_vertices}')
    blocks, weights = [], []
    for q, alpha in enumerate(fibers):
        for exponent, coefficient in alpha.terms:
            for copy in range(coefficient):
                blocks.append({'original_vertex': q, 'exponent': exponent.to_json(), 'copy': copy})
                weights.append(Ordinal.omega_power(exponent))
    edges = []
    for i, bi in enumerate(blocks):
        qi = bi['original_vertex']
        for j, bj in enumerate(blocks):
            qj = bj['original_vertex']
            if (qi == qj and i < j) or poset.succ[qi] >> qj & 1:
                edges.append((i, j))
    return Poset.from_edges(total, edges), weights, blocks


def frontier_height(poset: Poset, weights: list[Ordinal]) -> Ordinal:
    """Independent, compressed maximal-frontier DP; positive pure fibers only."""
    if not poset.n or any(not w.is_pure or w <= ONE for w in weights):
        raise ValueError('Compressed formula requires nonempty positive pure fibers')
    frontiers = poset.maximal_antichains()
    down = {a: poset.downclosure(a) for a in frontiers}
    ordered = sorted(frontiers, key=lambda a: down[a].bit_count())
    values = {a: ZERO for a in frontiers}
    for b in ordered:
        for a in ordered:
            if a != b and down[a] & ~down[b] == 0:
                cost = max(weights[q] for q in bits(a & ~b))
                values[b] = max(values[b], values[a] + cost)
    return max(values[a] + max(weights[q] for q in bits(a)) for a in ordered)


def solve(data: dict[str, Any], max_vertices: int = 20) -> dict[str, Any]:
    p = Poset.from_edges(data['n'], data.get('edges', []))
    fibers = [Ordinal.from_json(x) for x in data['fiber_types']]
    refined, weights, blocks = expand(p, fibers, max_vertices)
    _, cert = pure_height(refined, weights)
    if not check_certificate(cert):
        raise AssertionError('Internal certificate check failed')
    cert['source_input'] = data
    cert['blocks'] = blocks
    cert['certificate_checked'] = True
    return cert


def point_rank(data: dict[str, Any], generators: list[list[Any]],
               max_vertices: int = 20) -> dict[str, Any]:
    """Compute r(K) for K generated by [vertex, ordinal_position] pairs.

    The principal lower interval ending at K is K(K), whose height is r(K)+1.
    It has a finite cofinal set, so its expanded maximal blocks are singletons.
    """
    p = Poset.from_edges(data['n'], data.get('edges', []))
    fibers = [Ordinal.from_json(x) for x in data['fiber_types']]
    if len(fibers) != p.n:
        raise ValueError('fiber_types length must equal n')
    maxima: dict[int, Ordinal] = {}
    for pair in generators:
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError('A generator must be [vertex, ordinal_position]')
        q, position = pair
        if type(q) is not int or not 0 <= q < p.n:
            raise ValueError('Invalid generator vertex')
        x = Ordinal.from_json(position)
        if not x < fibers[q]:
            raise ValueError('Generator position must be strictly below its fiber')
        maxima[q] = max(maxima.get(q, ZERO), x)
    support = {q: x for q, x in maxima.items()
               if not any(p.succ[q] >> r & 1 for r in maxima)}
    local = []
    for q, alpha in enumerate(fibers):
        if any(p.succ[q] >> a & 1 for a in support):
            local.append(alpha)
        elif q in support:
            local.append(support[q] + ONE)
        else:
            local.append(ZERO)
    local_data = {'n': p.n, 'edges': data.get('edges', []),
                  'fiber_types': [x.to_json() for x in local]}
    cert = solve(local_data, max_vertices)
    h = Ordinal.from_json(cert['height'])
    if not h or h.terms[-1][0]:
        raise AssertionError('A principal lower interval must have successor height')
    tail = h.terms[-1][1] - 1
    rank = Ordinal(h.terms[:-1] + (((ZERO, tail),) if tail else ()))
    if rank + ONE != h:
        raise AssertionError('Successor-rank consistency failure')
    return {'rank': rank.to_json(), 'rank_text': str(rank),
            'original_input': data, 'generators': generators,
            'normalized_generators': [[q, x.to_json()] for q, x in sorted(support.items())],
            'lower_interval_certificate': cert}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--max-vertices', type=int, default=20,
                        help='Exponential-state-space safety limit (default 20)')
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding='utf-8'))
        answer = (point_rank(data, data['generators'], args.max_vertices)
                  if 'generators' in data else solve(data, args.max_vertices))
        text = json.dumps(answer, indent=2) + '\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
            print(answer.get('height_text', answer.get('rank_text')))
        else:
            print(text, end='')
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(2, f'error: {error}\n')


if __name__ == '__main__':
    main()
