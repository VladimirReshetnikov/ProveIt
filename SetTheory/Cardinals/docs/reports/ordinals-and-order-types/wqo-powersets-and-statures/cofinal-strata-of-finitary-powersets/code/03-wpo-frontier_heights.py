#!/usr/bin/env python3
"""Exact frontier-height calculus for finite lexicographic sums.

See article.tex for the transfinite theorem. This program evaluates its finite
formula; it does not compute an infinite rank by finite sampling.

CNFs are tuples ((priority, coefficient), ...) with decreasing priorities.
Positive priorities stand for an ordered list of positive ordinal exponents.
With no exponent_labels supplied, a priority p is displayed as the exponent p.
Only the order/equality of the priorities is used, not arithmetic on them.
Python 3.10+, standard library only.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Iterator, Sequence

CNF = tuple[tuple[int, int], ...]
ZERO: CNF = ()
ONE: CNF = ((0, 1),)


def natural_sum(a: CNF, b: CNF) -> CNF:
    """Hessenberg sum, used by tests and general bounds, NOT by the DP."""
    d = dict(a)
    for e, c in b:
        d[e] = d.get(e, 0) + c
    return tuple(sorted(d.items(), reverse=True))


def ordinal_add(a: CNF, b: CNF) -> CNF:
    """Ordinary ordinal addition of finite CNFs."""
    if not b:
        return a
    e, c = b[0]
    head = tuple((f, d) for f, d in a if f > e)
    previous = next((d for f, d in a if f == e), 0)
    return head + ((e, previous + c),) + b[1:]


def monomial(priority: int | None) -> CNF:
    return ZERO if priority is None else ((priority, 1),)


def parse_cnf(value: Any) -> CNF:
    if not isinstance(value, list):
        raise ValueError('CNF must be a list of [priority, coefficient] pairs')
    result: list[tuple[int, int]] = []
    for pair in value:
        if (not isinstance(pair, list) or len(pair) != 2
                or any(type(x) is not int for x in pair)):
            raise ValueError('invalid CNF pair')
        e, c = pair
        if e < 0 or c <= 0 or (result and e >= result[-1][0]):
            raise ValueError('CNF must have decreasing nonnegative priorities and positive coefficients')
        result.append((e, c))
    return tuple(result)


def format_cnf(a: CNF, labels: dict[str, str] | None = None) -> str:
    if not a:
        return '0'
    labels = labels or {}
    terms = []
    for e, c in a:
        if e == 0:
            terms.append(str(c))
            continue
        label = labels.get(str(e), str(e))
        term = 'omega' if label == '1' else f'omega^({label})'
        if c != 1:
            term += f'*{c}'
        terms.append(term)
    return ' + '.join(terms)


def bits(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Poset:
    n: int
    predecessors: tuple[int, ...]
    successors: tuple[int, ...]

    @classmethod
    def from_edges(cls, n: int, edges: Iterable[Sequence[int]]) -> Poset:
        if type(n) is not int or not 0 <= n <= 22:
            raise ValueError('n must be an integer from 0 to 22 (exponential-state safety guard)')
        succ = [0] * n
        for edge in edges:
            if len(edge) != 2 or any(type(v) is not int for v in edge):
                raise ValueError('edges must be integer pairs')
            a, b = edge
            if not (0 <= a < n and 0 <= b < n) or a == b:
                raise ValueError('edge endpoint out of range or self-loop')
            succ[a] |= 1 << b
        for k in range(n):
            for i in range(n):
                if succ[i] & (1 << k):
                    succ[i] |= succ[k]
        if any(succ[i] & (1 << i) for i in range(n)):
            raise ValueError('the relation contains a directed cycle')
        pred = [0] * n
        for i, mask in enumerate(succ):
            for j in bits(mask):
                pred[j] |= 1 << i
        return cls(n, tuple(pred), tuple(succ))

    @property
    def full(self) -> int:
        return (1 << self.n) - 1

    def is_ideal(self, mask: int) -> bool:
        return (0 <= mask <= self.full
                and all(self.predecessors[v] & ~mask == 0 for v in bits(mask)))

    def frontier(self, mask: int) -> int:
        return sum(1 << v for v in bits(mask) if self.successors[v] & mask == 0)

    def ideals(self) -> list[int]:
        return [s for s in range(self.full + 1) if self.is_ideal(s)]

    def edges(self) -> list[list[int]]:
        return [[v, w] for v in range(self.n) for w in bits(self.successors[v])]

    def extensions(self, mask: int = 0, prefix: tuple[int, ...] = ()) -> Iterator[tuple[int, ...]]:
        if mask == self.full:
            yield prefix
            return
        for v in range(self.n):
            if not mask & (1 << v) and self.predecessors[v] & ~mask == 0:
                yield from self.extensions(mask | (1 << v), prefix + (v,))


def validate_priorities(p: Poset, priorities: Sequence[int]) -> tuple[int, ...]:
    if len(priorities) != p.n or any(type(x) is not int or x <= 0 for x in priorities):
        raise ValueError('one strictly positive integer priority is required per vertex')
    return tuple(priorities)


def weight(mask: int, priorities: Sequence[int]) -> CNF:
    return monomial(max((priorities[v] for v in bits(mask)), default=None))


def path_value(p: Poset, priorities: Sequence[int], order: Sequence[int]) -> CNF:
    """Validate and value one linear extension using the theorem's formula."""
    validate_priorities(p, priorities)
    if len(order) != p.n or set(order) != set(range(p.n)):
        raise ValueError('order is not a permutation of the vertices')
    if p.n == 0:
        return ONE
    total, mask, front = ZERO, 0, 0
    for v in order:
        if p.predecessors[v] & ~mask:
            raise ValueError('order is not a linear extension')
        mask |= 1 << v
        new_front = p.frontier(mask)
        total = ordinal_add(total, weight(front & ~new_front, priorities))
        front = new_front
    return ordinal_add(total, weight(front, priorities))


def solve(p: Poset, priorities: Sequence[int]) -> dict[str, Any]:
    priorities = validate_priorities(p, priorities)
    ideals = p.ideals()
    front = {s: p.frontier(s) for s in ideals}
    values: dict[int, CNF] = {0: ZERO}
    pred: dict[int, tuple[int, int] | None] = {0: None}
    for s in ideals[1:]:
        best: CNF | None = None
        choice = None
        for v in bits(front[s]):
            previous = s ^ (1 << v)
            candidate = ordinal_add(values[previous], weight(front[previous] & ~front[s], priorities))
            if best is None or candidate > best:
                best, choice = candidate, (previous, v)
        assert best is not None and choice is not None
        values[s], pred[s] = best, choice
    order: list[int] = []
    s = p.full
    while s:
        step = pred[s]
        assert step is not None
        s, v = step
        order.append(v)
    order.reverse()
    answer = ONE if p.n == 0 else ordinal_add(values[p.full], weight(front[p.full], priorities))
    return {
        'schema': 'frontier-height-certificate-v1',
        'n': p.n, 'edges': p.edges(), 'priorities': list(priorities),
        'height_cnf': [list(t) for t in answer],
        'height': format_cnf(answer),
        'linear_extension': order,
        'state_count': len(ideals),
        'edge_count': sum(front[s].bit_count() for s in ideals),
        'states': [
            {'ideal': s, 'frontier': front[s],
             'value': [list(t) for t in values[s]],
             'predecessor': list(pred[s]) if pred[s] is not None else None}
            for s in ideals
        ],
    }


def verify_certificate(certificate: dict[str, Any]) -> bool:
    """Check all Bellman inequalities, one tight predecessor/state, and witness.

    No call to solve(). The checker validates the finite certificate, not the
    transfinite proof in the article. It raises ValueError on invalid input.
    """
    if certificate.get('schema') != 'frontier-height-certificate-v1':
        raise ValueError('unknown certificate schema')
    p = Poset.from_edges(certificate['n'], certificate['edges'])
    priorities = validate_priorities(p, certificate['priorities'])
    rows = certificate.get('states')
    if not isinstance(rows, list):
        raise ValueError('missing certificate states')
    states: dict[int, dict[str, Any]] = {}
    for row in rows:
        s = row['ideal']
        if type(s) is not int or s in states or not p.is_ideal(s):
            raise ValueError('duplicate or invalid ideal')
        if row['frontier'] != p.frontier(s):
            raise ValueError('incorrect frontier')
        states[s] = row
    if set(states) != set(p.ideals()):
        raise ValueError('incomplete state set')
    values = {s: parse_cnf(row['value']) for s, row in states.items()}
    if values[0] != ZERO or states[0]['predecessor'] is not None:
        raise ValueError('invalid initial state')
    for s, row in states.items():
        if not s:
            continue
        tight_edges = []
        for v in bits(p.frontier(s)):
            previous = s ^ (1 << v)
            candidate = ordinal_add(values[previous], weight(p.frontier(previous) & ~p.frontier(s), priorities))
            if candidate > values[s]:
                raise ValueError('violated Bellman upper-bound inequality')
            if candidate == values[s]:
                tight_edges.append([previous, v])
        if row['predecessor'] not in tight_edges:
            raise ValueError('chosen predecessor is not a tight valid edge')
    answer = ONE if p.n == 0 else ordinal_add(values[p.full], weight(p.frontier(p.full), priorities))
    if parse_cnf(certificate['height_cnf']) != answer:
        raise ValueError('incorrect terminal height')
    labels = certificate.get('exponent_labels', {})
    if (not isinstance(labels, dict)
            or any(not isinstance(k, str) or not isinstance(v, str) for k, v in labels.items())):
        raise ValueError('exponent_labels must map strings to strings')
    if certificate.get('height') != format_cnf(answer, labels):
        raise ValueError('height display does not match its CNF and labels')
    if path_value(p, priorities, certificate['linear_extension']) != answer:
        raise ValueError('linear extension does not attain certified height')
    if certificate['state_count'] != len(states):
        raise ValueError('incorrect state count')
    if certificate['edge_count'] != sum(p.frontier(s).bit_count() for s in states):
        raise ValueError('incorrect edge count')
    return True


def maximal_antichains(p: Poset) -> list[int]:
    """Inclusion-maximal antichains, sorted by their generated downsets."""
    found = []
    for a in range(p.full + 1):
        if any(p.successors[v] & a for v in bits(a)):
            continue
        comparable = a
        for v in bits(a):
            comparable |= p.predecessors[v] | p.successors[v]
        if comparable == p.full:
            found.append(a)
    return sorted(found, key=lambda a: downclosure(p, a))


def downclosure(p: Poset, a: int) -> int:
    result = a
    for v in bits(a):
        result |= p.predecessors[v]
    return result


def solve_compressed(p: Poset, priorities: Sequence[int]) -> tuple[CNF, list[int]]:
    """Independent DP on maximal antichains using all strict Hoare edges.

    Returns the height and an attaining chain of maximal-antichain bitmasks.
    This routine shares ordinal arithmetic but not the support-state DP.
    """
    validate_priorities(p, priorities)
    if p.n == 0:
        return ONE, [0]
    antichains = maximal_antichains(p)
    down = {a: downclosure(p, a) for a in antichains}
    value: dict[int, CNF] = {}
    previous: dict[int, int | None] = {}
    for a in antichains:
        candidates = [(ordinal_add(value[b], weight(b & ~a, priorities)), b)
                      for b in value if down[b] & ~down[a] == 0]
        if candidates:
            best = max(v for v, _ in candidates)
            value[a] = best
            previous[a] = next(b for v, b in candidates if v == best)
        else:
            value[a], previous[a] = ZERO, None
    top = p.frontier(p.full)
    chain = []
    a: int | None = top
    while a is not None:
        chain.append(a)
        a = previous[a]
    chain.reverse()
    return ordinal_add(value[top], weight(top, priorities)), chain


def expand_limit_fibers(p: Poset, cnfs: Sequence[Sequence[Sequence[int]]]) -> tuple[Poset, tuple[int, ...], list[int]]:
    """Expand positive limit-ordinal fibers in finite CNF into pure blocks.

    Each coefficient is expanded literally, so the size guard applies to the
    expanded skeleton. Priorities must be positive and decreasing per fiber.
    """
    if len(cnfs) != p.n:
        raise ValueError('one nonempty limit CNF is required per vertex')
    owners, priorities, blocks = [], [], []
    for q, raw in enumerate(cnfs):
        cnf = parse_cnf([list(pair) for pair in raw])
        if not cnf or cnf[-1][0] == 0:
            raise ValueError('fiber CNFs must describe positive limit ordinals')
        ids = []
        for e, c in cnf:
            if len(priorities) + c > 22:
                raise ValueError('expanded skeleton exceeds the 22-vertex guard')
            for _ in range(c):
                ids.append(len(priorities))
                priorities.append(e)
                owners.append(q)
        blocks.append(ids)
    edges = []
    for ids in blocks:
        edges.extend([a, b] for a, b in zip(ids, ids[1:]))
    for q, r in p.edges():
        edges.extend([a, b] for a in blocks[q] for b in blocks[r])
    return Poset.from_edges(len(priorities), edges), tuple(priorities), owners


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON instance or certificate')
    parser.add_argument('--check', action='store_true', help='check a saved certificate')
    parser.add_argument('--output', type=Path, help='save full certificate JSON')
    args = parser.parse_args()
    try:
        instance = json.loads(args.input.read_text(encoding='utf-8'))
        if args.check:
            verify_certificate(instance)
            print('Certificate valid (finite computation only).')
            return
        p = Poset.from_edges(instance['n'], instance.get('edges', []))
        owners = None
        if 'fiber_cnfs' in instance:
            p, priorities, owners = expand_limit_fibers(p, instance['fiber_cnfs'])
        else:
            priorities = instance['priorities']
        result = solve(p, priorities)
        labels = instance.get('exponent_labels', {})
        if (not isinstance(labels, dict)
                or any(not isinstance(k, str) or not isinstance(v, str) for k, v in labels.items())):
            raise ValueError('exponent_labels must map strings to strings')
        result['height'] = format_cnf(parse_cnf(result['height_cnf']), labels)
        if labels:
            result['exponent_labels'] = labels
        if owners is not None:
            result['expanded_block_owners'] = owners
        verify_certificate(result)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({k: v for k, v in result.items() if k != 'states'}, indent=2))
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(2, f'error: {exc}\n')


if __name__ == '__main__':
    main()
