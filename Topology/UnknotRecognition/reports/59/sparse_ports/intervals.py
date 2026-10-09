"""Interval-union coverage oracle over an injected exact orbit-count backend."""
from __future__ import annotations
from typing import Callable
from .core import ResourceLimit, natural, valid_mask


def canonical_union(intervals):
    merged = []
    for lo, hi in sorted(intervals):
        if lo == hi:
            continue
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    return tuple(merged)


def prepare_ports(size, ports):
    natural(size, 'size')
    answer = []
    for port in ports:
        intervals = []
        for item in port:
            if len(item) != 2:
                raise ValueError('marked interval needs two endpoints')
            lo, hi = natural(item[0]), natural(item[1])
            if not 0 <= lo <= hi <= size:
                raise ValueError('marked interval leaves the universe')
            intervals.append((lo, hi))
        answer.append(canonical_union(intervals))
    return tuple(answer)


def selected_union(ports, mask):
    return canonical_union(interval for i, port in enumerate(ports)
                           if mask & (1 << i) for interval in port)


def cone_rows(union):
    if not union:
        return []
    hub = union[0][0]
    rows = []
    for lo, hi in union:
        if hi - lo > 1:
            rows.append((lo, hi-2, lo+1, hi-1, 1))
        if lo != hub:
            rows.append((hub, hub, lo, lo, 1))
    return rows


class IntervalOracle:
    """Cache exact physical unions, never just equal numerical query values.

    backend(extra_rows) returns an exact integer orbit count. It owns the
    shared AHT cycle allowance and optional local proof recording. Rows have
    inclusive endpoints and sign +1/-1. Mark intervals are half-open.
    """
    def __init__(self, size, ports, backend: Callable, *,
                 max_calls=None, check=None):
        self.ports = prepare_ports(size, ports)
        self.r = len(self.ports)
        self.full = (1 << self.r)-1
        self.backend = backend
        self.max_calls = max_calls
        if max_calls is not None:
            natural(max_calls, 'max_calls')
        self.check = check or (lambda: None)
        self.calls = self.cache_hits = self.zeta_requests = 0
        self.cache = {}
        self.total = self._count([])

    def _count(self, extra):
        self.check()
        if self.max_calls is not None and self.calls >= self.max_calls:
            raise ResourceLimit('orbit-call allowance exhausted')
        self.calls += 1
        return natural(self.backend(extra), 'orbit count')

    def __call__(self, u):
        self.check(); valid_mask(u, self.r); self.zeta_requests += 1
        union = selected_union(self.ports, self.full ^ u)
        if not union:
            return self.total
        if union not in self.cache:
            value = self._count(cone_rows(union)) - 1
            if not 0 <= value <= self.total:
                raise ArithmeticError('invalid coned orbit count')
            self.cache[union] = value
        else:
            self.cache_hits += 1
        # G(U)=C-Coverage(complement U)=coned_count-1, for nonempty union.
        return self.cache[union]


def dense_reference(oracle: IntervalOracle):
    """Controlled dense ablation; same backend/cache as sparse, r<=20 only."""
    r = oracle.r
    if r > 20:
        raise ResourceLimit('explicit dense reference limited to 20 ports')
    values = [oracle(u) for u in range(1 << r)]
    for i in range(r):
        for u in range(1 << r):
            if u & (1 << i):
                values[u] -= values[u ^ (1 << i)]
    return {u: w for u, w in enumerate(values) if w}
