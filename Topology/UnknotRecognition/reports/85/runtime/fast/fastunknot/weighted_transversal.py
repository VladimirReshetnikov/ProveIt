"""Exact orbit weights attached to compressed least original representatives.

Histogram counts alone do not identify which original component owns a
weight. Tagged selector intervals retain that association without expanding
points. Only monotone, forward AHT traces are supported.
"""
from math import gcd

from .integer_codec import encoded_integer
from .interval_orbits import count_orbits
from .interval_orbit_verify import verify_orbit_certificate, _transmitted_row
from .orbit_transversal import _contract_live, _retain_prefix
from .weighted_orbits import (_prepare_weights, _contract_weights, _contract_rows,
                              _truncate_translation, _truncate_reflection, _conservation)


def _canonical_tags(tags, check):
    result = []
    for lo, hi, value in sorted(tags):
        check()
        if result and lo < result[-1][1]: raise ArithmeticError('weighted representatives overlap')
        if result and lo == result[-1][1] and value == result[-1][2]:
            result[-1] = (result[-1][0], hi, value)
        else: result.append((lo, hi, value))
    return result


def _emit(runs, live, gaps, check):
    """Intersect three ordered partitions and retain original source labels."""
    source = []; position = 0
    for lo, hi in live:
        source.append((position, position+hi-lo, lo)); position += hi-lo
    ri = si = 0; output = []
    for first, last in gaps:
        point, end = first, last+1
        while point < end:
            check()
            while runs[ri][1] <= point: ri += 1
            while source[si][1] <= point: si += 1
            stop = min(end, runs[ri][1], source[si][1])
            label = source[si][2]+point-source[si][0]
            output.append((label, label+stop-point, runs[ri][2]))
            point = stop
    return output


def _tagged_replay(size, dimension, initial, proof, check):
    if any(e['op'] not in ('delete', 'trim', 'merge', 'transmit', 'contract', 'truncate') for e in proof['operations']):
        raise ValueError('weighted least representatives require a monotone orbit trace')
    rows = [[encoded_integer(x) for x in r] for r in proof['pairings']]
    runs = initial; live = [(0, size)] if size else []; tags = []; histogram = {}
    stats = dict(trace_events=0, maximum_live_intervals=len(live), maximum_weight_runs=len(runs))
    for event in proof['operations']:
        check(); stats['trace_events'] += 1; operation = event['op']
        if operation == 'delete': rows.pop(encoded_integer(event['index']))
        elif operation == 'trim':
            i = encoded_integer(event['index']); a, _, _, d, _ = rows[i]; b = (a+d-1)//2
            rows[i] = [a, b, a+d-b, d, -1]
        elif operation == 'merge':
            i, j = sorted((encoded_integer(event['left']), encoded_integer(event['right'])))
            a, b, c, d, _ = rows[i]; aa, bb, cc, dd, _ = rows[j]
            period = gcd(c-a, cc-aa); lo, hi = min(a, aa), max(d, dd)
            rows[i] = [lo, hi-period, lo+period, hi, 1]; rows.pop(j)
        elif operation == 'transmit':
            i, j = encoded_integer(event['transmitter']), encoded_integer(event['target'])
            rows[j] = _transmitted_row(rows[i], rows[j], event['source_power'], event['target_power'], size)
        elif operation == 'contract':
            gaps = [[encoded_integer(x) for x in gap] for gap in event['gaps']]
            tags.extend(_emit(runs, live, gaps, check))
            runs, _ = _contract_weights(runs, size, gaps, histogram, check)
            live = _contract_live(live, [(lo, hi+1) for lo, hi in gaps], [], check)
            rows = _contract_rows(rows, gaps); size -= sum(hi-lo+1 for lo, hi in gaps)
        else:
            i, cut = encoded_integer(event['index']), encoded_integer(event['new_size'])
            a, b, c, d, sign = rows[i]
            runs = (_truncate_translation(runs, size, cut, c-a, dimension, check) if sign == 1 else
                    _truncate_reflection(runs, size, cut, a, dimension, check))
            live = _retain_prefix(live, cut, check); removed = size-cut
            if cut == c: rows.pop(i)
            elif sign == 1: rows[i] = [a, b-removed, c, cut-1, 1]
            else: rows[i] = [a+removed, b, c, cut-1, -1]
            size = cut
        stats['maximum_live_intervals'] = max(stats['maximum_live_intervals'], len(live))
        stats['maximum_weight_runs'] = max(stats['maximum_weight_runs'], len(runs))
    if size or rows or runs or live: raise ArithmeticError('weighted transversal trace did not finish')
    tags = _canonical_tags(tags, check)
    tagged_histogram = {}
    for lo, hi, value in tags: tagged_histogram[value] = tagged_histogram.get(value, 0)+hi-lo
    if tagged_histogram != histogram: raise ArithmeticError('tagged representatives and orbit weights disagree')
    histogram = [dict(weight=list(v), orbits=n) for v, n in sorted(histogram.items())]
    _conservation(initial, histogram, dimension)
    if sum(hi-lo for lo, hi, _ in tags) != encoded_integer(proof['orbit_count']):
        raise ArithmeticError('weighted representative cardinality disagrees')
    stats['representative_runs'] = len(tags)
    return [dict(start=lo, stop=hi, weight=list(v)) for lo, hi, v in tags], histogram, stats


def _answer(size, dimension, runs, proof, check, record_certificate, extra):
    tags, histogram, stats = _tagged_replay(size, dimension, runs, proof, check); stats.update(extra)
    result = dict(status='COMPLETE', orbit_count=encoded_integer(proof['orbit_count']),
                  representative_runs=tags, histogram=histogram, stats=stats)
    if record_certificate:
        weighted = dict(schema='weighted-interval-orbits-v1', size=size, dimension=dimension,
                        weights=[[lo, hi, list(v)] for lo, hi, v in runs], orbit_proof=proof, histogram=histogram)
        result['certificate'] = dict(schema='weighted-orbit-transversal-v1', weighted_certificate=weighted, representative_runs=tags)
    check(); return result


def weighted_orbit_transversal(size, pairings, weight_intervals, *, dimension=None, max_cycles=None,
                               check=None, record_certificate=False):
    """Discover exact component weights at least original representatives."""
    poll = check if check is not None else lambda: None; poll()
    if type(record_certificate) is not bool: raise ValueError('record_certificate must be bool')
    size, dimension, runs = _prepare_weights(size, weight_intervals, dimension, poll)
    counted = count_orbits(size, list(pairings), max_cycles=max_cycles, sweep_direction='forward', check=poll, record_certificate=True)
    if not counted.complete:
        return dict(status='INCONCLUSIVE', stats=dict(orbit_cycles=counted.cycles))
    return _answer(size, dimension, runs, counted.certificate, poll, record_certificate, dict(orbit_cycles=counted.cycles))


def weighted_transversal_from_orbit_certificate(size, pairings, weight_intervals, orbit_certificate, *,
                                                dimension=None, check=None, record_certificate=False):
    """Reuse an independently authenticated complete monotone orbit trace."""
    poll = check if check is not None else lambda: None; poll()
    if type(record_certificate) is not bool: raise ValueError('record_certificate must be bool')
    size, dimension, runs = _prepare_weights(size, weight_intervals, dimension, poll)
    if not verify_orbit_certificate(size, list(pairings), orbit_certificate, check=poll): raise ValueError('invalid source orbit trace')
    return _answer(size, dimension, runs, orbit_certificate, poll, record_certificate, dict(reused_orbit_certificate=True))
