"""Binary weighted orbit histograms from independently replayable AHT traces.

The orbit algorithm is Agol--Hass--Thurston's maintained implementation.
This module adds exact piecewise-constant integer-vector weight transport.
Each histogram entry describes the sum of original weights on one orbit,
and records how many orbits have that sum. No represented point is expanded.

Weights are additive half-open intervals ``(start, stop, vector)``. They may
overlap and signed coordinates are permitted. Unmarked points have zero
weight. The independent checker is in ``weighted_orbit_verify``.
"""

from bisect import bisect_left
from math import gcd

from .integer_codec import encoded_integer
from .interval_orbits import count_orbits
from .interval_orbit_verify import _transmitted_row, verify_orbit_certificate


def _integer(value, name, minimum=None):
    try:
        value = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f'{name} must be an integer or hexadecimal string') from exc
    if minimum is not None and value < minimum:
        raise ValueError(f'{name} must be at least {minimum}')
    return value


def _add(delta, lo, hi, value, multiplier=1):
    """Add a constant vector to a half-open interval in difference form."""
    if lo == hi or not multiplier or not any(value):
        return
    for endpoint, sign in ((lo, multiplier), (hi, -multiplier)):
        row = delta.setdefault(endpoint, [0] * len(value))
        for j, entry in enumerate(value):
            row[j] += sign * entry


def _canonical(size, dimension, delta, check, start=0):
    """Turn endpoint differences into a covering, coalesced run list."""
    if start == size:
        return []
    endpoints = sorted(set(delta) | {start, size})
    value = [0] * dimension
    runs = []
    for lo, hi in zip(endpoints, endpoints[1:]):
        check()
        for j, entry in enumerate(delta.get(lo, ())):
            value[j] += entry
        _append(runs, lo, hi, tuple(value))
    return runs


def _overlay_prefix(runs, cut, lower, upper, delta, dimension, check):
    """Add transported weights only on their image, reusing untouched tuples.

    The old run partition is canonical. Runs strictly before the image can
    therefore be copied without vector addition or equality comparisons.
    At the image and its boundary, coalescing restores the canonical partition.
    """
    added = _canonical(upper, dimension, delta, check, start=lower)
    active = [any(value) for _, _, value in added]
    result, index, unchanged_tail = [], 0, False
    for lo, hi, value in runs:
        check()
        if lo >= cut:
            break
        hi = min(hi, cut)
        if hi <= lower:
            result.append((lo, hi, value))
            continue
        if unchanged_tail:
            result.append((lo, hi, value))
            continue
        if lo < lower:
            result.append((lo, lower, value))
            lo = lower
        while lo < min(hi, upper):
            check()
            while added[index][1] <= lo:
                index += 1
            stop = min(hi, added[index][1])
            combined = (tuple(a+b for a, b in zip(value, added[index][2]))
                        if active[index] else value)
            _append(result, lo, stop, combined)
            lo = stop
        if lo < hi:
            _append(result, lo, hi, value)
            unchanged_tail = True
    return result


def _append(runs, lo, hi, value):
    if lo == hi:
        return
    if runs and runs[-1][1] == lo and runs[-1][2] == value:
        runs[-1] = (runs[-1][0], hi, value)
    else:
        runs.append((lo, hi, value))


def _prepare_weights(size, weight_intervals, dimension, check):
    size = _integer(size, 'size', 0)
    if not isinstance(weight_intervals, (tuple, list)):
        raise ValueError('weight_intervals must be an explicit list or tuple')
    if dimension is None:
        if weight_intervals:
            first = weight_intervals[0]
            if (not isinstance(first, (tuple, list)) or len(first) != 3
                    or not isinstance(first[2], (tuple, list))):
                raise ValueError('each weight interval requires start, stop and vector')
            dimension = len(first[2])
        else:
            dimension = 1
    dimension = _integer(dimension, 'dimension', 1)
    delta = {}
    for record in weight_intervals:
        check()
        if not isinstance(record, (tuple, list)) or len(record) != 3:
            raise ValueError('each weight interval requires start, stop and vector')
        lo, hi = (_integer(record[i], 'weight endpoint', 0) for i in (0, 1))
        if not 0 <= lo <= hi <= size:
            raise ValueError('weight interval is outside the universe')
        vector = record[2]
        if not isinstance(vector, (tuple, list)) or len(vector) != dimension:
            raise ValueError('weight vectors must have the requested dimension')
        vector = tuple(_integer(value, 'weight coordinate') for value in vector)
        _add(delta, lo, hi, vector)
    return size, dimension, _canonical(size, dimension, delta, check)


def _truncate_translation(runs, size, cut, period, dimension, check):
    """Push a suffix modulo period, using quotient and remainder intervals."""
    base = cut - period
    delta = {}
    for lo, hi, value in runs:
        check()
        left = max(lo, cut)
        if left >= hi:
            continue
        quotient, remainder = divmod(hi - left, period)
        _add(delta, base, cut, value, quotient)
        start = base + (left - base) % period
        first = min(remainder, cut - start)
        _add(delta, start, start + first, value)
        _add(delta, base, base + remainder - first, value)
    return _overlay_prefix(runs, cut, base, cut, delta, dimension, check)


def _truncate_reflection(runs, size, cut, left_endpoint, dimension, check):
    """Push the deleted suffix through x -> left_endpoint + size - 1 - x."""
    delta = {}
    for lo, hi, value in runs:
        check()
        left = max(lo, cut)
        if left < hi:
            _add(delta, left_endpoint + size - hi,
                 left_endpoint + size - left, value)
    return _overlay_prefix(runs, cut, left_endpoint, left_endpoint+size-cut,
                           delta, dimension, check)


def _contract_weights(runs, size, gaps, histogram, check):
    """Emit singleton representative weights and close the static gaps."""
    if not runs:
        return [], 0
    cuts = sorted({0, size}
                  | {endpoint for lo, hi, _ in runs for endpoint in (lo, hi)}
                  | {endpoint for lo, hi in gaps for endpoint in (lo, hi + 1)})
    run_index = gap_index = removed = emitted = 0
    result = []
    for lo, hi in zip(cuts, cuts[1:]):
        check()
        while runs[run_index][1] <= lo:
            run_index += 1
        while gap_index < len(gaps) and gaps[gap_index][1] < lo:
            gap_index += 1
        value = runs[run_index][2]
        if gap_index < len(gaps) and gaps[gap_index][0] <= lo:
            histogram[value] = histogram.get(value, 0) + hi - lo
            removed += hi - lo
            emitted += 1
        else:
            _append(result, lo - removed, hi - removed, value)
    return result, emitted


def _contract_rows(rows, gaps):
    ends = [hi for _, hi in gaps]
    sums = [0]
    for lo, hi in gaps:
        sums.append(sums[-1] + hi - lo + 1)
    return [[endpoint - sums[bisect_left(ends, endpoint)] for endpoint in row[:4]]
            + [row[4]] for row in rows]


def _replay(size, dimension, runs, proof, check):
    """Transport weights along a trusted, complete maintained AHT trace.

    Public replay validates the unweighted trace before entering this helper.
    Generation enters with a trace produced in the same call by count_orbits.
    """
    rows = [[encoded_integer(value) for value in row] for row in proof['pairings']]
    histogram = {}
    stats = dict(input_weight_runs=len(runs), maximum_weight_runs=len(runs),
                 translation_pushes=0, reflection_pushes=0,
                 emitted_weight_runs=0, replay_events=0)
    for event in proof['operations']:
        check()
        stats['replay_events'] += 1
        operation = event['op']
        if operation == 'delete':
            rows.pop(encoded_integer(event['index']))
        elif operation == 'trim':
            index = encoded_integer(event['index'])
            a, _, _, d, _ = rows[index]
            b = (a + d - 1) // 2
            rows[index] = [a, b, a + d - b, d, -1]
        elif operation == 'merge':
            i, j = sorted((encoded_integer(event['left']), encoded_integer(event['right'])))
            a, b, c, d, _ = rows[i]
            aa, bb, cc, dd, _ = rows[j]
            period = gcd(c-a, cc-aa)
            lo, hi = min(a, aa), max(d, dd)
            rows[i] = [lo, hi-period, lo+period, hi, 1]
            rows.pop(j)
        elif operation == 'transmit':
            i = encoded_integer(event['transmitter'])
            j = encoded_integer(event['target'])
            rows[j] = _transmitted_row(rows[i], rows[j], event['source_power'],
                                      event['target_power'], size)
        elif operation == 'contract':
            gaps = [[encoded_integer(value) for value in gap] for gap in event['gaps']]
            runs, emitted = _contract_weights(runs, size, gaps, histogram, check)
            stats['emitted_weight_runs'] += emitted
            rows = _contract_rows(rows, gaps)
            size -= sum(hi-lo+1 for lo, hi in gaps)
        elif operation == 'truncate':
            i, cut = encoded_integer(event['index']), encoded_integer(event['new_size'])
            a, b, c, d, sign = rows[i]
            if sign == 1:
                runs = _truncate_translation(runs, size, cut, c-a, dimension, check)
                stats['translation_pushes'] += 1
            else:
                runs = _truncate_reflection(runs, size, cut, a, dimension, check)
                stats['reflection_pushes'] += 1
            removed = size-cut
            if cut == c:
                rows.pop(i)
            elif sign == 1:
                rows[i] = [a, b-removed, c, cut-1, 1]
            else:
                rows[i] = [a+removed, b, c, cut-1, -1]
            size = cut
        else:
            raise ArithmeticError('unknown trusted orbit event')
        stats['maximum_weight_runs'] = max(stats['maximum_weight_runs'], len(runs))
    if size or rows or runs:
        raise ArithmeticError('weighted replay did not finish')
    result = [dict(weight=list(value), orbits=count)
              for value, count in sorted(histogram.items())]
    if sum(record['orbits'] for record in result) != encoded_integer(proof['orbit_count']):
        raise ArithmeticError('weighted and unweighted orbit counts disagree')
    return result, stats


def _conservation(runs, histogram, dimension):
    before = [sum((hi-lo)*value[j] for lo, hi, value in runs) for j in range(dimension)]
    after = [sum(row['orbits']*row['weight'][j] for row in histogram)
             for j in range(dimension)]
    if before != after:
        raise ArithmeticError('weighted orbit sum was not conserved')


def _result(size, dimension, runs, proof, check, record_certificate, stats_extra):
    histogram, stats = _replay(size, dimension, runs, proof, check)
    _conservation(runs, histogram, dimension)
    stats.update(stats_extra)
    answer = dict(status='COMPLETE', orbit_count=encoded_integer(proof['orbit_count']),
                  histogram=histogram, stats=stats)
    if record_certificate:
        answer['certificate'] = dict(schema='weighted-interval-orbits-v1', size=size,
            dimension=dimension, weights=[[lo, hi, list(value)] for lo, hi, value in runs],
            orbit_proof=proof, histogram=histogram)
    check()
    return answer


def weighted_orbit_histogram(size, pairings, weight_intervals, *, dimension=None,
                             max_cycles=None, periodic_rule='fine_wilf', check=None,
                             record_certificate=False):
    """Count component weight sums in binary input size, without point expansion.

    ``max_cycles`` and cancellation belong to the underlying AHT query.
    INCONCLUSIVE replies have no histogram or certificate. A complete query
    creates an unweighted trace internally even when record_certificate=False,
    since weight transport needs its exact sequence of contractions.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    size, dimension, runs = _prepare_weights(size, weight_intervals, dimension, poll)
    pairs = list(pairings)
    counted = count_orbits(size, pairs, max_cycles=max_cycles, periodic_rule=periodic_rule,
                           check=poll, record_certificate=True)
    if not counted.complete:
        return dict(status='INCONCLUSIVE',
                    stats=dict(orbit_cycles=counted.cycles, orbit_stats=dict(counted.stats)))
    return _result(size, dimension, runs, counted.certificate, poll, record_certificate,
                   dict(orbit_cycles=counted.cycles, orbit_stats=dict(counted.stats)))


def weighted_histogram_from_orbit_certificate(size, pairings, weight_intervals,
                                             orbit_certificate, *, dimension=None,
                                             check=None, record_certificate=False):
    """Reuse a supplied orbit trace after checking its exact source and steps."""
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    size, dimension, runs = _prepare_weights(size, weight_intervals, dimension, poll)
    if not verify_orbit_certificate(size, list(pairings), orbit_certificate, check=poll):
        raise ValueError('the supplied orbit certificate failed independent replay')
    return _result(size, dimension, runs, orbit_certificate, poll, record_certificate,
                   dict(reused_orbit_certificate=True))
