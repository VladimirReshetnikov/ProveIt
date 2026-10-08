"""A proved object bound and a deterministic choice of mirror for exact windows."""
from __future__ import annotations
from time import monotonic

from .diagram import DisjointSet
from .geometry import SMOOTHINGS, ScanLimit
from .window_scan import khovanov_window, validate_seconds


def state_circle_count(diagram, smoothing, *, check=lambda: None):
    if smoothing not in (0, 1):
        raise ValueError("smoothing must be zero or one")
    if not diagram.pd:
        return 1
    dsu = DisjointSet(2 * diagram.crossings)
    for index, row in enumerate(diagram.pd):
        if not index & 255:
            check()
        for a, b in SMOOTHINGS[smoothing]:
            dsu.union(row[a], row[b])
    return len({dsu.find(e) for e in range(2 * diagram.crossings)})


def weighted_binomial_sum(n, k, *, check=lambda: None):
    """Return sum(2**j * binomial(n,j), j=0..k), with exact integer arithmetic."""
    if not 0 <= k <= n:
        raise ValueError("require 0 <= k <= n")
    term = total = 1
    for j in range(1, k + 1):
        if not j & 255:
            check()
        term = term * (n - j + 1) * 2 // j
        total += term
    return total


def choose_mirror(diagram, lower, upper, *, check=lambda: None):
    """Minimize the proved cube-object upper bound, not an empirical time predictor."""
    n = diagram.crossings
    if type(lower) is not int or type(upper) is not int or lower > upper:
        raise ValueError("lower and upper must be integers with lower <= upper")
    a, b = max(0, lower), min(n, upper)
    if a > b:
        return False, {"mirrored": False, "empty_target": True}
    check()
    s0 = state_circle_count(diagram, 0, check=check)
    s1 = state_circle_count(diagram, 1, check=check)
    k0, k1 = min(n, b + 1), min(n, n - a + 1)
    bound0 = (1 << s0) * weighted_binomial_sum(n, k0, check=check)
    bound1 = (1 << s1) * weighted_binomial_sum(n, k1, check=check)
    check()
    mirrored = bound1 < bound0
    return mirrored, {"mirrored": mirrored, "empty_target": False,
                       "all_zero_circles": s0, "all_one_circles": s1,
                       "original_depth": k0, "mirror_depth": k1,
                       "original_bound_bits": bound0.bit_length(),
                       "mirror_bound_bits": bound1.bit_length(),
                       "selection": "minimum exact proved object upper bound"}


def khovanov_window_auto(diagram, lower, upper, **options):
    """Compute a raw window, selecting a mirror and restoring original raw degrees."""
    started = monotonic()
    seconds = options.get('seconds')
    validate_seconds(seconds)
    deadline = None if seconds is None else started + seconds
    def check():
        if deadline is not None and monotonic() > deadline:
            raise ScanLimit("time budget exhausted during mirror selection")
    check()
    mirrored, choice = choose_mirror(diagram, lower, upper, check=check)
    n = diagram.crossings
    work = diagram.mirror() if mirrored else diagram
    check()
    a, b = (n - upper, n - lower) if mirrored else (lower, upper)
    if options.get('seconds') is not None:
        options['seconds'] = max(0.0, options['seconds'] - (monotonic() - started))
    result = khovanov_window(work.pd, a, b, **options)
    if mirrored:
        result['by_degree'] = dict(sorted((n - h, rank) for h, rank in result['by_degree'].items()))
    result.update(raw_lower=lower, raw_upper=upper, orientation=choice,
                  profile_degree_convention='mirror raw' if mirrored else 'original raw')
    return result

