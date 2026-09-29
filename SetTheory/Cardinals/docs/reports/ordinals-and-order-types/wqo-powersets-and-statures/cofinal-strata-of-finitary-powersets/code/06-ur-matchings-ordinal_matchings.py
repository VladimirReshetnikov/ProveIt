#!/usr/bin/env python3
"""Exact first-neighbour ordinal scheduling, with checkable DP certificates.

Standard-library-only; Python 3.10+. Exponents are positive integers, not floats.
A CNF is a tuple ((exponent, coefficient), ...) in decreasing exponent order.
The terminal exponent is kept separately, including when residual graphs are empty.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

CNF = tuple[tuple[int, int], ...]


def add_monomial(value: CNF, exponent: int) -> CNF:
    """Ordinary ordinal addition of omega**exponent (0 means no summand)."""
    if exponent == 0:
        return value
    kept = [(e, c) for e, c in value if e >= exponent]
    if kept and kept[-1][0] == exponent:
        kept[-1] = (exponent, kept[-1][1] + 1)
    else:
        kept.append((exponent, 1))
    return tuple(kept)


def parse_cnf(value: Any) -> CNF:
    if not isinstance(value, (list, tuple)):
        raise ValueError('A CNF must be a list of [exponent, coefficient] pairs.')
    result: list[tuple[int, int]] = []
    previous: int | None = None
    for pair in value:
        if not isinstance(pair, (list, tuple)) or len(pair) != 2:
            raise ValueError('Malformed CNF term.')
        e, c = pair
        if type(e) is not int or type(c) is not int or e < 1 or c < 1:
            raise ValueError('CNF exponents and coefficients must be positive integers.')
        if previous is not None and e >= previous:
            raise ValueError('CNF exponents must be strictly decreasing.')
        result.append((e, c))
        previous = e
    return tuple(result)


def format_cnf(value: CNF) -> str:
    if not value:
        return '0'
    return ' + '.join(('omega' if e == 1 else f'omega^{e}')
                      + ('' if c == 1 else f'*{c}') for e, c in value)


@dataclass(frozen=True)
class Instance:
    """Rows are lower vertices, columns upper vertices; zero rows are excluded."""
    row_masks: tuple[int, ...]
    priorities: tuple[int, ...]
    upper_count: int
    terminal: int

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> 'Instance':
        if not isinstance(data, dict):
            raise ValueError('The instance must be a JSON object.')
        n = data.get('upper_count')
        tau = data.get('terminal')
        rows = data.get('neighbours')
        priorities = data.get('priorities')
        if type(n) is not int or n < 0:
            raise ValueError('upper_count must be a nonnegative integer.')
        if type(tau) is not int or tau < 1:
            raise ValueError('terminal must be a positive integer.')
        if not isinstance(rows, list) or not isinstance(priorities, list):
            raise ValueError('neighbours and priorities must be lists.')
        if len(rows) != len(priorities):
            raise ValueError('One priority is required for every lower vertex.')
        if any(type(p) is not int or p < 1 for p in priorities):
            raise ValueError('Priorities must be positive integers.')
        masks = []
        for row in rows:
            if not isinstance(row, list) or not row:
                raise ValueError('Every lower vertex must have a nonempty neighbour list.')
            if any(type(u) is not int or not 0 <= u < n for u in row):
                raise ValueError('Upper vertex index outside 0,...,upper_count-1.')
            if len(set(row)) != len(row):
                raise ValueError('Duplicate neighbour indices are not allowed.')
            masks.append(sum(1 << u for u in row))
        return cls(tuple(masks), tuple(priorities), n, tau)

    def to_dict(self) -> dict[str, Any]:
        return {'upper_count': self.upper_count,
                'neighbours': [[u for u in range(self.upper_count) if mask >> u & 1]
                               for mask in self.row_masks],
                'priorities': list(self.priorities), 'terminal': self.terminal}

    def weight(self, processed: int, upper: int) -> int:
        bit = 1 << upper
        return max((p for mask, p in zip(self.row_masks, self.priorities)
                    if mask & bit and not mask & processed), default=0)

    def schedule(self, order: Sequence[int]) -> tuple[CNF, list[dict[str, Any]]]:
        if (not isinstance(order, (list, tuple))
                or any(type(u) is not int for u in order)
                or sorted(order) != list(range(self.upper_count))):
            raise ValueError('The schedule must be a permutation of all upper vertices.')
        value: CNF = ()
        processed = 0
        groups = []
        for u in order:
            fresh = [i for i, mask in enumerate(self.row_masks)
                     if mask >> u & 1 and not mask & processed]
            p = max((self.priorities[i] for i in fresh), default=0)
            value = add_monomial(value, p)
            groups.append({'upper': u, 'new_lower': fresh, 'priority': p})
            processed |= 1 << u
        return add_monomial(value, self.terminal), groups


def solve(instance: Instance, max_columns: int = 22) -> dict[str, Any]:
    """Subset DP, O(2^s s (r+d)) elementary work; no implicit compression."""
    s = instance.upper_count
    if s > max_columns:
        raise ValueError(f'{s} upper vertices exceed the chosen guard {max_columns}.')
    values: list[CNF] = [()] * (1 << s)
    parents = [-1] * (1 << s)
    for mask in range(1, 1 << s):
        best: CNF | None = None
        for u in range(s):
            if mask >> u & 1:
                previous = mask ^ (1 << u)
                candidate = add_monomial(values[previous], instance.weight(previous, u))
                if best is None or candidate > best:
                    best, parents[mask] = candidate, u
        assert best is not None
        values[mask] = best
    mask = (1 << s) - 1
    order = []
    while mask:
        u = parents[mask]
        order.append(u)
        mask ^= 1 << u
    order.reverse()
    value, groups = instance.schedule(order)
    assert value == add_monomial(values[-1], instance.terminal)
    return {'format': 'ordinal-first-neighbour-dp-v1',
            'instance': instance.to_dict(),
            'value': value, 'value_text': format_cnf(value),
            'order': order, 'groups': groups,
            'states': [{'value': v, 'last': p} for v, p in zip(values, parents)]}


def solve_by_covered_rows(instance: Instance, max_rows: int = 22) -> CNF:
    """Dual exact DP on covered lower rows, not on used upper columns.

    A previously used column has no uncovered neighbour, so every productive
    transition is automatically an unused column. This removes the need to
    remember the used-column set. Returns the value, not a certificate.
    """
    r, s = len(instance.row_masks), instance.upper_count
    if r > max_rows:
        raise ValueError(f'{r} lower rows exceed the chosen guard {max_rows}.')
    columns = [sum(1 << i for i, row in enumerate(instance.row_masks) if row >> u & 1)
               for u in range(s)]
    values: list[CNF | None] = [None] * (1 << r)
    values[0] = ()
    for covered in range(1 << r):
        value = values[covered]
        if value is None:
            continue
        for neighbours in columns:
            fresh = neighbours & ~covered
            if not fresh:
                continue
            exponent = max(instance.priorities[i] for i in range(r) if fresh >> i & 1)
            target = covered | neighbours
            candidate = add_monomial(value, exponent)
            if values[target] is None or candidate > values[target]:
                values[target] = candidate
    result = values[-1]
    if result is None:
        raise ValueError('A lower row has no neighbour; the instance is invalid.')
    return add_monomial(result, instance.terminal)


def check_certificate(instance: Instance, certificate: dict[str, Any],
                      max_columns: int = 22) -> bool:
    """Check every Bellman inequality plus an attaining predecessor.

    This checker does not call solve(), but shares validated CNF arithmetic.
    It establishes the finite optimum, not the transfinite interpretation.
    """
    if not isinstance(certificate, dict):
        raise ValueError('The certificate must be a JSON object.')
    if instance.upper_count > max_columns:
        raise ValueError('Certificate exceeds the chosen state-space guard.')
    if certificate.get('format') != 'ordinal-first-neighbour-dp-v1':
        raise ValueError('Unknown certificate format.')
    if certificate.get('instance') != instance.to_dict():
        raise ValueError('The certificate is for a different instance.')
    states = certificate.get('states')
    if not isinstance(states, list) or len(states) != 1 << instance.upper_count:
        raise ValueError('Incorrect number of certificate states.')
    if any(not isinstance(state, dict) for state in states):
        raise ValueError('Every certificate state must be a JSON object.')
    values = [parse_cnf(state['value']) for state in states]
    if values[0] or states[0].get('last') != -1:
        raise ValueError('Bad base state.')
    for mask in range(1, len(states)):
        last = states[mask].get('last')
        if type(last) is not int or not 0 <= last < instance.upper_count or not mask >> last & 1:
            raise ValueError('Invalid predecessor witness.')
        for u in range(instance.upper_count):
            if mask >> u & 1:
                previous = mask ^ (1 << u)
                candidate = add_monomial(values[previous], instance.weight(previous, u))
                if candidate > values[mask]:
                    raise ValueError('A Bellman upper-bound inequality fails.')
                if u == last and candidate != values[mask]:
                    raise ValueError('A selected predecessor does not attain the state value.')
    expected = add_monomial(values[-1], instance.terminal)
    if parse_cnf(certificate.get('value')) != expected:
        raise ValueError('Incorrect terminal value.')
    value, groups = instance.schedule(certificate.get('order', []))
    if value != expected:
        raise ValueError('The supplied schedule does not attain the optimum.')
    if certificate.get('groups') != groups:
        raise ValueError('The claimed retirement groups are incorrect.')
    return True


def compress_twins(instance: Instance) -> Instance:
    """Safe weighted compression: equal neighbourhoods only, never containment."""
    row_types: dict[int, int] = {}
    for mask, p in zip(instance.row_masks, instance.priorities):
        row_types[mask] = max(row_types.get(mask, 0), p)
    rows = list(row_types)
    col_types: dict[tuple[int, ...], int] = {}
    old_to_new: dict[int, int] = {}
    for u in range(instance.upper_count):
        typ = tuple(i for i, mask in enumerate(rows) if mask >> u & 1)
        if not typ:  # contributes only through the retained terminal exponent
            continue
        if typ not in col_types:
            col_types[typ] = len(col_types)
        old_to_new[u] = col_types[typ]
    new_rows: dict[int, int] = {}
    for mask, p in row_types.items():
        new_mask = 0
        for u, v in old_to_new.items():
            if mask >> u & 1:
                new_mask |= 1 << v
        new_rows[new_mask] = max(new_rows.get(new_mask, 0), p)
    return Instance(tuple(new_rows), tuple(new_rows.values()), len(col_types), instance.terminal)


def triangular_order(instance: Instance, matching: Sequence[tuple[int, int]]) -> tuple[int, ...] | None:
    """Return matching-edge indices in an admissible order, or None on a cycle.

    Arc i->j means lower_i is adjacent to upper_j (i != j). Thus i must
    appear before j if lower_i is to remain a fresh witness for upper_i.
    """
    if len({i for i, _ in matching}) != len(matching) or len({u for _, u in matching}) != len(matching):
        raise ValueError('The edge list is not a matching.')
    for i, u in matching:
        if not 0 <= i < len(instance.row_masks) or not 0 <= u < instance.upper_count:
            raise ValueError('Invalid matching endpoint.')
        if not instance.row_masks[i] >> u & 1:
            raise ValueError('A claimed matching edge is absent.')
    k = len(matching)
    arcs = [set() for _ in range(k)]
    indegree = [0] * k
    for i, (ell, _) in enumerate(matching):
        for j, (_, u) in enumerate(matching):
            if i != j and instance.row_masks[ell] >> u & 1:
                arcs[i].add(j)
                indegree[j] += 1
    stack = [i for i in range(k) if indegree[i] == 0]
    order = []
    while stack:
        i = stack.pop()
        order.append(i)
        for j in arcs[i]:
            indegree[j] -= 1
            if indegree[j] == 0:
                stack.append(j)
    return tuple(order) if len(order) == k else None


def enumerate_matchings(instance: Instance) -> Iterable[tuple[tuple[int, int], ...]]:
    """Exponential independent validator; not used by the production DP."""
    chosen: list[tuple[int, int]] = []
    def visit(row: int, used: int) -> Iterable[tuple[tuple[int, int], ...]]:
        if row == len(instance.row_masks):
            yield tuple(chosen)
            return
        yield from visit(row + 1, used)
        available = instance.row_masks[row] & ~used
        while available:
            bit = available & -available
            available ^= bit
            u = bit.bit_length() - 1
            chosen.append((row, u))
            yield from visit(row + 1, used | bit)
            chosen.pop()
    return visit(0, 0)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    sp = sub.add_parser('solve')
    sp.add_argument('input', type=Path)
    sp.add_argument('--output', type=Path)
    sp.add_argument('--max-columns', type=int, default=22)
    cp = sub.add_parser('check')
    cp.add_argument('input', type=Path)
    cp.add_argument('certificate', type=Path)
    cp.add_argument('--max-columns', type=int, default=22)
    args = parser.parse_args()
    try:
        instance = Instance.from_dict(json.loads(args.input.read_text(encoding='utf-8')))
        if args.command == 'solve':
            certificate = solve(instance, args.max_columns)
            check_certificate(instance, certificate, args.max_columns)
            text = json.dumps(certificate, indent=2) + '\n'
            if args.output:
                args.output.write_text(text, encoding='utf-8')
                print(certificate['value_text'])
            else:
                print(text, end='')
        else:
            certificate = json.loads(args.certificate.read_text(encoding='utf-8'))
            check_certificate(instance, certificate, args.max_columns)
            print('VALID: ' + format_cnf(parse_cnf(certificate['value'])))
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(2, f'error: {error}\n')


if __name__ == '__main__':
    main()
