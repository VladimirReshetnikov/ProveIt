"""Halo-safe extremal windows and an exact/UNKNOWN decision interface.

A low window retains degrees through k+1, AFTER exhaustive cancellation.
It reports only degrees through k. The halo degree is never interpreted as
true homology. Mirror windows implement the upper end without sign heuristics.
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass, field
from math import comb
from time import monotonic
from .geometry import ScanLimit
from .orders import certify, nice_order, OrderError
from .scanner import ScanComplex

@dataclass
class WindowResult:
    depth: int
    n: int
    ranks: dict[int, int]
    certificate: object
    stats: dict
    stages: list[dict] = field(default_factory=list)
    def rank(self, r: int) -> int:
        if not 0 <= r <= self.depth:
            raise ValueError('degree is outside the certified output window')
        return self.ranks.get(r, 0)

@dataclass
class ProbeResult:
    verdict: str
    known_ranks: dict[int, int]
    n_negative: int
    reason: str
    runs: list[dict] = field(default_factory=list)


def erase_above(scan, cutoff: int) -> None:
    """Drop a brutal-truncation tail through the documented ScanComplex API."""
    ids = [ident for ident, (_, h) in scan.objects.items() if h > cutoff]
    for ident in ids:
        for target in list(scan.out.get(ident, {})):
            scan._set(ident, target, 0)
        for source in list(scan.inc.get(ident, set())):
            scan._set(source, ident, 0)
        del scan.objects[ident]
        scan.out.pop(ident, None)
        scan.inc.pop(ident, None)


def low_window(diagram, depth: int, *, order=None, pivot='minfill', max_objects=None,
               deadline=None, scanner_factory=ScanComplex, trace=False,
               assert_binomial=True) -> WindowResult:
    n = len(diagram.pd)
    if type(depth) is not int or depth < 0:
        raise ValueError('depth must be a nonnegative integer')
    depth = min(depth, n)
    if order is None:
        try:
            cert = nice_order(diagram.pd)
        except OrderError:
            cert = certify(diagram.pd, range(n))
    else:
        cert = certify(diagram.pd, order)
    if not n:
        return WindowResult(0, 0, {0: 2}, cert, {'max_objects_before_elimination': 2}, [])
    scan = scanner_factory(max_objects=max_objects, deadline=deadline, pivot=pivot)
    cutoff, stages = min(n, depth + 1), []
    for t, crossing in enumerate(cert.order, 1):
        # Do not suppress the temporary degree cutoff+1. Its cancellations can
        # remove artificial classes in the retained halo.
        scan.add_crossing(tuple(diagram.pd[crossing]), reduce_now=True)
        erase_above(scan, cutoff)
        profile = Counter(h for _, h in scan.objects.values())
        if cert.nice and assert_binomial:
            factor = 2 if t == n else 1
            for h, count in profile.items():
                if not 0 <= h <= t or count > factor * comb(t, h):
                    raise ArithmeticError(f'binomial invariant failed at stage {t}, degree {h}: {count}')
        if trace:
            stages.append({'stage': t, 'objects': len(scan.objects),
                           'profile': dict(sorted(profile.items())),
                           'matching_profile': sorted((h, tuple(sorted(tuple(sorted(p)) for p in m)), count)
                            for (m, h), count in Counter(scan.objects.values()).items())})
    ranks = {h: d for h, d in scan.linear_ranks().items() if h <= depth and d}
    stats = dict(scan.stats)
    stats['algebra'] = dict(scan.algebra.stats)
    stats['retained_final'] = len(scan.objects)
    return WindowResult(depth, n, ranks, cert, stats, stages)


def probe(diagram, depth: int, *, order=None, pivot='minfill', max_objects=None,
          seconds=None, scanner_factory=ScanComplex, limit_exceptions=(ScanLimit,)) -> ProbeResult:
    """Two endpoint windows. UNKNOWN is mandatory if unexamined degrees remain."""
    if type(depth) is not int or depth < 0:
        raise ValueError('depth must be a nonnegative integer')
    if seconds is not None and seconds <= 0:
        raise ValueError('seconds must be positive')
    n = len(diagram.pd)
    nneg = sum(s < 0 for s in diagram.signs())
    known, runs = {}, []
    deadline = None if seconds is None else monotonic() + seconds
    def result(reason, verdict='UNKNOWN'):
        return ProbeResult(verdict, dict(sorted(known.items())), nneg, reason, runs)
    for side, dgm in (('low', diagram), ('high', diagram.mirror())):
        try:
            w = low_window(dgm, depth, order=order, pivot=pivot, max_objects=max_objects,
                           deadline=deadline, scanner_factory=scanner_factory)
        except limit_exceptions as exc:
            return result(f'resource ceiling: {exc}')
        runs.append({'side': side, 'depth': w.depth, 'nice': w.certificate.nice,
                     'girth': w.certificate.girth, 'stats': w.stats})
        for j in range(w.depth + 1):
            r = j if side == 'low' else n - j
            value = w.rank(j)
            if r in known and known[r] != value:
                raise ArithmeticError('overlapping mirror windows disagree')
            known[r] = value
            expected = 2 if r == nneg else 0
            if value != expected:
                return result(f'certified rank {value} in normalized degree {r - nneg}, expected {expected}', 'NONTRIVIAL')
    missing = set(range(n + 1)) - known.keys()
    if not missing:
        return result('complete homological profile agrees with the unknot', 'UNKNOT')
    if missing == {nneg}:
        # Jones(1)=1 gives the normalized total Euler characteristic 2.
        # This argument is valid only for a validated one-component diagram.
        return result('all off-zero homology vanishes; Euler characteristic determines degree zero', 'UNKNOT')
    return result('unexamined degrees remain; no negative inference is permitted')


def adaptive_probe(diagram, *, max_depth=None, seconds=None, **kwargs) -> ProbeResult:
    """Geometric-depth restarts. Complete unless an explicit resource cap stops it."""
    n = len(diagram.pd)
    if max_depth is not None and (type(max_depth) is not int or max_depth < 0):
        raise ValueError('max_depth must be a nonnegative integer')
    if seconds is not None and seconds <= 0:
        raise ValueError('seconds must be positive')
    ceiling = (n + 1) // 2 if max_depth is None else min(max_depth, (n + 1) // 2)
    end = None if seconds is None else monotonic() + seconds
    depth, history = 0, []
    while True:
        remaining = None if end is None else end - monotonic()
        if remaining is not None and remaining <= 0:
            return ProbeResult('UNKNOWN', {}, sum(s < 0 for s in diagram.signs()), 'adaptive time budget exhausted', history)
        r = probe(diagram, depth, seconds=remaining, **kwargs)
        history.extend(r.runs); r.runs = history[:]
        if r.verdict != 'UNKNOWN' or depth == ceiling or r.reason.startswith('resource ceiling'):
            return r
        depth = min(ceiling, 1 if depth == 0 else 2 * depth)
