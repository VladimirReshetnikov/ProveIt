"""Compressed least representatives of a supplied interval equivalence relation.

The result is a union of half-open intervals in the ORIGINAL point universe.
Every original orbit meets that union in exactly one point, its least point.
An interval can contain arbitrarily many representatives; those points are
never expanded.  This is a trace compiler for the maintained AHT kernel.

The independent checker uses reverse gap insertion instead of this module's
forward surviving-source intervals.  No claim about knot provenance is made.
Only order-preserving universe reductions are supported: a global reflect
event is rejected even if the underlying orbit-count certificate is valid.
"""

from .integer_codec import encoded_integer
from .interval_orbits import count_orbits
from .interval_orbit_verify import verify_orbit_certificate


def _size(value):
    try:
        value = encoded_integer(value)
    except ValueError as exc:
        raise ValueError('size must be an integer or hexadecimal string') from exc
    if value < 0:
        raise ValueError('size must be nonnegative')
    return value


def _append(intervals, lo, hi):
    if lo >= hi:
        return
    if intervals and intervals[-1][1] == lo:
        intervals[-1] = (intervals[-1][0], hi)
    else:
        intervals.append((lo, hi))


def _contract_live(live, gaps, emitted, check):
    """Delete current-rank gaps, retaining their ORIGINAL labels as answers."""
    remaining, position, gap_index = [], 0, 0
    for source_lo, source_hi in live:
        check()
        stop = position + source_hi - source_lo
        cursor = position
        while cursor < stop:
            check()
            while gap_index < len(gaps) and gaps[gap_index][1] <= cursor:
                gap_index += 1
            if gap_index == len(gaps) or gaps[gap_index][0] >= stop:
                _append(remaining, source_lo + cursor - position, source_hi)
                break
            gap_lo, gap_hi = gaps[gap_index]
            if cursor < gap_lo:
                until = min(stop, gap_lo)
                _append(remaining, source_lo + cursor - position,
                        source_lo + until - position)
            else:
                until = min(stop, gap_hi)
                # Emission order need not be original point order.
                emitted.append((source_lo + cursor - position,
                                source_lo + until - position))
            cursor = until
        position = stop
    return remaining


def _retain_prefix(live, cut, check):
    remaining, available = [], cut
    for lo, hi in live:
        check()
        if not available:
            break
        used = min(hi - lo, available)
        _append(remaining, lo, lo + used)
        available -= used
    if available:
        raise ArithmeticError('trusted truncation exceeds the surviving source')
    return remaining


def _forward_selector(size, proof, check):
    """Compile a complete trusted trace; public replay verifies it first."""
    live = [(0, size)] if size else []
    emitted = []
    current = size
    stats = dict(trace_events=0, contraction_gap_intervals=0, truncations=0,
                 maximum_live_intervals=len(live))
    unchanged = {'delete', 'trim', 'merge', 'transmit'}
    for event in proof['operations']:
        check()
        stats['trace_events'] += 1
        operation = event['op']
        if operation == 'contract':
            gaps = [(encoded_integer(lo), encoded_integer(hi) + 1)
                    for lo, hi in event['gaps']]
            stats['contraction_gap_intervals'] += len(gaps)
            live = _contract_live(live, gaps, emitted, check)
            current -= sum(hi - lo for lo, hi in gaps)
        elif operation == 'truncate':
            cut = encoded_integer(event['new_size'])
            live = _retain_prefix(live, cut, check)
            current = cut
            stats['truncations'] += 1
        elif operation not in unchanged:
            raise ValueError('least transversals require a monotone orbit trace; '
                             'unsupported operation: '+str(operation))
        stats['maximum_live_intervals'] = max(stats['maximum_live_intervals'], len(live))
    if current or live:
        raise ArithmeticError('trusted orbit trace did not finish')
    representatives = []
    for lo, hi in sorted(emitted):
        check()
        if representatives and lo < representatives[-1][1]:
            raise ArithmeticError('source representatives overlap')
        _append(representatives, lo, hi)
    count = sum(hi - lo for lo, hi in representatives)
    if count != encoded_integer(proof['orbit_count']):
        raise ArithmeticError('transversal cardinality disagrees with the orbit trace')
    # Reverse gap insertion proves this stronger bound on the final union.
    if len(representatives) > stats['contraction_gap_intervals']:
        raise ArithmeticError('the compressed transversal exceeds its interval bound')
    stats.update(emitted_intervals_before_coalescing=len(emitted),
                 representative_intervals=len(representatives))
    return representatives, count, stats


def _answer(size, proof, check, record_certificate, discovery_stats):
    representatives, count, stats = _forward_selector(size, proof, check)
    stats.update(discovery_stats)
    intervals = [list(interval) for interval in representatives]
    result = dict(status='COMPLETE', orbit_count=count,
                  representative_intervals=intervals, stats=stats)
    if record_certificate:
        result['certificate'] = dict(schema='interval-orbit-transversal-v1', size=size,
            orbit_proof=proof, orbit_count=count, representative_intervals=intervals)
    check()
    return result


def orbit_transversal(size, pairings, *, max_cycles=None, periodic_rule='fine_wilf',
                      check=None, record_certificate=False):
    """Discover an AHT trace and return compressed least orbit representatives.

    The cycle allowance meters only AHT discovery.  Later trace compilation
    has its explicit trace size and cooperative callback.  An incomplete
    result has no representative set, orbit count, or certificate.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    size = _size(size)
    counted = count_orbits(size, list(pairings), max_cycles=max_cycles,
                          periodic_rule=periodic_rule, check=poll, record_certificate=True,
                          sweep_direction='forward')
    if not counted.complete:
        return dict(status='INCONCLUSIVE', reason='orbit-cycle allowance exhausted',
                    stats=dict(orbit_cycles=counted.cycles, orbit_stats=dict(counted.stats)))
    return _answer(size, counted.certificate, poll, record_certificate,
                   dict(orbit_cycles=counted.cycles, orbit_stats=dict(counted.stats)))


def transversal_from_orbit_certificate(size, pairings, orbit_certificate, *,
                                       check=None, record_certificate=False):
    """Compile a supplied complete monotone trace after independent replay.

    A valid orbit-count proof with global reflection is outside this
    compiler's order-preserving contract and raises ValueError.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    size = _size(size)
    if not verify_orbit_certificate(size, list(pairings), orbit_certificate, check=poll):
        raise ValueError('the supplied orbit certificate failed independent replay')
    return _answer(size, orbit_certificate, poll, record_certificate,
                   dict(reused_orbit_certificate=True))
