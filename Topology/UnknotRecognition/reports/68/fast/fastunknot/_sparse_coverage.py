"""Exact nonnegative subset-sum recovery; no interval or knot assumptions.

The existence of a nonnegative measure is a precondition. Independent
certification for interval inputs is in sparse_incidence_verify.py.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations
from collections.abc import Callable
import re


class WorkLimit(RuntimeError):
    """An explicit local resource allowance was exhausted."""


def integer(value: object) -> int:
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', value):
        return int(value, 16)
    raise ValueError('expected an integer or signed hexadecimal string')


def validate_options(strategy, max_signatures):
    if strategy not in ('linear', 'split'):
        raise ValueError('strategy must be linear or split')
    if max_signatures is not None and (type(max_signatures) is not int or max_signatures < 0):
        raise ValueError('max_signatures must be nonnegative or None')


def recover_nonnegative(r: int, total: int, query: Callable[[int], int], *,
                        strategy: str = 'linear', max_signatures: int | None = None,
                        check: Callable[[], None] | None = None) -> dict:
    """Recover h >= 0 from G(U)=sum_{T subset U} h(T).

    Returns positive entries only, in an inclusion-compatible peeling order.
    ``linear`` makes at most r trials per positive nonempty entry. ``split``
    uses balanced block deletion, adapting to small signature cardinalities.
    Raw values, NOT residual values, are cached. No prior sparsity bound needed.
    WorkLimit is raised rather than returning a partially certified histogram.
    """
    if type(r) is not int or r < 0 or type(total) is not int or total < 0:
        raise ValueError('r and total must be nonnegative integers')
    validate_options(strategy, max_signatures)
    poll = check if check is not None else (lambda: None)
    full = (1 << r) - 1
    raw = {full: total}
    entries: list[dict] = []
    extracted = 0
    trials = 0
    residual_terms = 0

    def residual(mask: int) -> int:
        nonlocal residual_terms
        poll()
        if mask not in raw:
            value = query(mask)
            if type(value) is not int or not 0 <= value <= total:
                raise ArithmeticError('invalid exact subset-sum answer')
            raw[mask] = value
        value = raw[mask]
        for entry in entries:
            poll()
            residual_terms += 1
            if entry['mask'] & mask == entry['mask']:
                value -= entry['weight']
        if not 0 <= value <= total - extracted:
            raise ArithmeticError('oracle violates nonnegative residual invariant')
        return value

    def append(mask: int, weight: int, zeros: list[list[int]]) -> None:
        nonlocal extracted
        if max_signatures is not None and len(entries) >= max_signatures:
            raise WorkLimit('signature allowance exhausted')
        if weight <= 0:
            raise ArithmeticError('peeling requires a positive atom')
        entries.append(dict(mask=mask, weight=weight, zeros=zeros))
        extracted += weight

    poll()
    if total:
        empty_weight = residual(0)
        if empty_weight:
            append(0, empty_weight, [])
    while extracted < total:
        poll()
        if max_signatures is not None and len(entries) >= max_signatures:
            raise WorkLimit('signature allowance exhausted')
        current = full
        zeros = []
        if strategy == 'linear':
            for bit in range(r):
                poll()
                candidate = current & ~(1 << bit)
                trials += 1
                if residual(candidate):
                    current = candidate
                else:
                    zeros.append([bit, candidate])
        else:
            stack = [(0, r)] if r else []
            while stack:
                poll()
                lo, hi = stack.pop()
                block = ((1 << (hi - lo)) - 1) << lo
                candidate = current & ~block
                trials += 1
                if residual(candidate):
                    current = candidate
                elif hi - lo == 1:
                    zeros.append([lo, candidate])
                else:
                    mid = (lo + hi) // 2
                    stack.append((mid, hi))
                    stack.append((lo, mid))
        append(current, residual(current), zeros)
    needed = {full}
    for entry in entries:
        needed.add(entry['mask'])
        needed.update(mask for _, mask in entry['zeros'])
    poll()
    return dict(entries=entries, needed=needed,
                stats=dict(subset_values=len(raw), deletion_trials=trials,
                           residual_terms=residual_terms, signatures=len(entries)))
