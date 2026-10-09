"""Exact sparse inversion of a nonnegative Boolean zeta transform.

This module knows nothing about knots or interval pairings.  Its oracle must
return G(U) = sum(h[T] for T subset U), with nonnegative integer h[T].
Masks have r bits; the algorithm never allocates a 2**r array.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Callable, Iterable


class ResourceLimit(RuntimeError):
    """An unfinished computation; never a zero count or a knot verdict."""


def natural(x: object, name: str = 'value') -> int:
    if type(x) is not int or x < 0:
        raise ValueError(f'{name} must be a nonnegative integer, not bool')
    return x


def valid_mask(x: object, r: int) -> int:
    x = natural(x, 'mask')
    if x.bit_length() > r:
        raise ValueError('mask contains an out-of-range port')
    return x


@dataclass(frozen=True)
class SparseResult:
    r: int
    total: int
    entries: tuple[tuple[int, int], ...]  # discovery order, positive weights
    oracle_requests: int
    residual_evaluations: int

    def as_dict(self) -> dict[int, int]:
        return dict(self.entries)


def recover(r: int, total: int, zeta: Callable[[int], int], *,
            strategy: str = 'split', max_entries: int | None = None,
            max_requests: int | None = None,
            check: Callable[[], None] | None = None) -> SparseResult:
    """Recover every positive coefficient, without knowing support size.

    'linear' greedily tries individual deletions; 'split' first tries whole
    balanced blocks. Requests count calls to zeta, including repeated masks.
    The caller may separately cache masks/marked unions. No partial result is
    returned after ResourceLimit or a callback exception. Exactness presumes
    the nonnegative-zeta oracle contract; this is not a test of that contract.
    """
    natural(r, 'r'); natural(total, 'total')
    for cap in (max_entries, max_requests):
        if cap is not None:
            natural(cap, 'allowance')
    if strategy not in ('linear', 'split'):
        raise ValueError('strategy must be linear or split')
    poll = check or (lambda: None)
    full = (1 << r) - 1
    found: list[tuple[int, int]] = []
    remaining = total
    requests = evaluations = 0

    def residual(u: int) -> int:
        nonlocal requests, evaluations
        poll(); evaluations += 1
        if u == full:
            raw = total
        else:
            if max_requests is not None and requests >= max_requests:
                raise ResourceLimit('zeta-request allowance exhausted')
            requests += 1
            raw = natural(zeta(u), 'oracle value')
            if raw > total:
                raise ArithmeticError('oracle value exceeds total')
        value = raw
        for t, weight in found:
            poll()
            if t & u == t:
                value -= weight
        if not 0 <= value <= remaining:
            raise ArithmeticError('oracle violates a residual nonnegativity bound')
        return value

    poll()
    while remaining:
        if max_entries is not None and len(found) >= max_entries:
            raise ResourceLimit('support allowance exhausted')
        u, value = full, remaining
        if strategy == 'linear':
            for i in range(r):
                poll()
                candidate = u & ~(1 << i)
                trial = residual(candidate)
                if trial:
                    u, value = candidate, trial
        elif r:
            # Iterative traversal avoids dependence on Python recursion limits.
            stack = [(0, r)]
            while stack:
                poll()
                lo, hi = stack.pop()
                block = ((1 << (hi - lo)) - 1) << lo
                candidate = u & ~block
                trial = residual(candidate)
                if trial:
                    u, value = candidate, trial
                elif hi - lo > 1:
                    mid = (lo + hi) // 2
                    stack.extend(((mid, hi), (lo, mid)))
        # When r==0, the sole coefficient equals the supplied total.
        if value <= 0 or any(t == u for t, _ in found):
            raise ArithmeticError('invalid or repeated extracted coefficient')
        found.append((u, value))
        remaining -= value
    poll()
    return SparseResult(r, total, tuple(found), requests, evaluations)


def certificate_queries(result: SparseResult) -> tuple[int, ...]:
    """Masks sufficient for the independent minimal-support certificate."""
    masks = set()
    for t, _ in result.entries:
        masks.add(t)
        bits = t
        while bits:
            bit = bits & -bits
            masks.add(t ^ bit)
            bits ^= bit
    return tuple(sorted(masks))


def certificate_payload(result: SparseResult) -> dict:
    return {'version': 1, 'ports': result.r, 'total': result.total,
            'entries': [list(item) for item in result.entries]}


def verify_payload(r: int, total: int, payload: object,
                   authenticated_zeta: Callable[[int], int], *,
                   check: Callable[[], None] | None = None) -> bool:
    """Independent algebraic replay; does not run recover or trust its order.

    authenticated_zeta must verify the underlying count/source binding, or
    raise ValueError. Its callback exceptions other than ValueError propagate.
    Tests of T and T minus each of its individual bits prove exact recovery
    inductively. Total-mass equality proves the absence of unlisted signatures.
    """
    poll = check or (lambda: None)
    try:
        natural(r, 'r'); natural(total, 'total'); poll()
        if not isinstance(payload, dict) or set(payload) != {
                'version', 'ports', 'total', 'entries'}:
            return False
        if (type(payload['version']) is not int or payload['version'] != 1
                or natural(payload['ports']) != r
                or natural(payload['total']) != total
                or not isinstance(payload['entries'], list)):
            return False
        previous: list[tuple[int, int]] = []
        seen: set[int] = set()
        mass = 0
        for item in payload['entries']:
            poll()
            if not isinstance(item, (list, tuple)) or len(item) != 2:
                return False
            t, w = valid_mask(item[0], r), natural(item[1], 'multiplicity')
            if w == 0 or t in seen or mass + w > total:
                return False
            # Deliberately not the producer's residual closure.
            probes = [t]
            for i in range(r):
                if (t >> i) & 1:
                    probes.append(t - (1 << i))
            for index, u in enumerate(probes):
                poll()
                value = natural(authenticated_zeta(u), 'authenticated value')
                if value > total:
                    return False
                prior = sum(v for a, v in previous if a | u == u)
                if value - prior != (w if index == 0 else 0):
                    return False
            previous.append((t, w)); seen.add(t); mass += w
        return mass == total
    except (ValueError, KeyError, TypeError):
        return False


def cone_update(entries: Iterable[tuple[int, int]], ports: int) -> dict[int, int]:
    """Exact update when *all* points in the selected port union are coned.

    NOT a model for an arbitrary attachment map or pointwise intersection.
    """
    natural(ports, 'selected ports')
    result: dict[int, int] = {}
    combined = 0
    touched = False
    for mask, weight in entries:
        natural(mask, 'signature'); natural(weight, 'multiplicity')
        if not weight:
            continue
        if mask & ports:
            combined |= mask
            touched = True
        else:
            result[mask] = result.get(mask, 0) + weight
    if touched:
        result[combined] = result.get(combined, 0) + 1
    return result


def union_relabel(entries: Iterable[tuple[int, int]],
                  new_ports: Iterable[int]) -> dict[int, int]:
    """Each new port is a union of old ports, specified by an old-port mask."""
    labels = tuple(natural(x, 'new-port mask') for x in new_ports)
    result: dict[int, int] = {}
    for mask, weight in entries:
        natural(mask, 'signature'); natural(weight, 'multiplicity')
        target = sum(1 << i for i, selected in enumerate(labels)
                     if mask & selected)
        if weight:
            result[target] = result.get(target, 0) + weight
    return result
