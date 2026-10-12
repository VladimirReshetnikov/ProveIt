"""Independent weighted representative replay by reverse gap insertion."""
from bisect import bisect_right
from collections import defaultdict
from math import gcd

from .integer_codec import encoded_integer
from .weighted_orbit_verify import (verify_weighted_orbit_certificate, _initial_weights, _canonical_pairings,
    _contract_weights, _translation_fold, _reflection_fold, _move_interval, _InvalidWeightedProof)


def _coalesce(rows, check):
    answer = []
    for lo, hi, value in sorted(rows):
        check()
        if answer and lo < answer[-1][1]: raise _InvalidWeightedProof('overlapping weighted selectors')
        if answer and lo == answer[-1][1] and value == answer[-1][2]: answer[-1] = (answer[-1][0], hi, value)
        else: answer.append((lo, hi, value))
    return answer


def _reverse_tags(size, pairs, runs, trace, dimension, check):
    history = []; histogram = defaultdict(int)
    for event in trace:
        check(); kind = event['op']
        if kind == 'delete': del pairs[encoded_integer(event['index'])]
        elif kind == 'trim':
            i = encoded_integer(event['index']); a, _, _, d, _ = pairs[i]; end = (a+d-1)//2
            pairs[i] = [a, end, a+d-end, d, -1]
        elif kind == 'merge':
            i, j = sorted((encoded_integer(event['left']), encoded_integer(event['right'])))
            a, _, c, d, _ = pairs[i]; aa, _, cc, dd, _ = pairs[j]; period = gcd(c-a, cc-aa)
            lo, hi = min(a, aa), max(d, dd); pairs[i] = [lo, hi-period, lo+period, hi, 1]; del pairs[j]
        elif kind == 'transmit':
            i, j = encoded_integer(event['transmitter']), encoded_integer(event['target'])
            carrier = pairs[i]; a, b, c, d, sign = pairs[j]
            a, b, sa = _move_interval(a, b, carrier, encoded_integer(event['source_power']))
            c, d, sb = _move_interval(c, d, carrier, encoded_integer(event['target_power']))
            if c < a: a, b, c, d = c, d, a, b
            pairs[j] = [a, b, c, d, sign*sa*sb]
        elif kind == 'contract':
            gaps = [[encoded_integer(x) for x in gap] for gap in event['gaps']]; emitted = []
            ri = 0
            for lo, hi in gaps:
                point, stop = lo, hi+1
                while point < stop:
                    check()
                    while runs[ri][1] <= point: ri += 1
                    end = min(stop, runs[ri][1]); emitted.append((point, end, runs[ri][2])); point = end
            history.append((gaps, emitted))
            runs, size = _contract_weights(runs, size, gaps, histogram, check)
            def shift(point): return point-sum(hi-lo+1 for lo, hi in gaps if hi < point)
            pairs = [[shift(a), shift(b), shift(c), shift(d), s] for a, b, c, d, s in pairs]
        elif kind == 'truncate':
            i, cut = encoded_integer(event['index']), encoded_integer(event['new_size']); a, b, c, d, sign = pairs[i]
            runs = (_translation_fold(runs, size, cut, c-a, dimension, check) if sign == 1 else
                    _reflection_fold(runs, size, cut, a+d, dimension, check))
            history.append((None, [])); removed = size-cut
            if cut == c: del pairs[i]
            elif sign == 1: pairs[i] = [a, b-removed, c, cut-1, 1]
            else: pairs[i] = [a+removed, b, c, cut-1, -1]
            size = cut
        else: raise _InvalidWeightedProof('weighted selectors require a monotone trace')
    if size or pairs or runs: raise _InvalidWeightedProof('incomplete weighted selector trace')
    selected = []
    for gaps, emitted in reversed(history):
        check()
        if gaps is None: continue
        anchors, prefix = [], [0]
        for lo, hi in gaps:
            anchors.append(lo-prefix[-1]); prefix.append(prefix[-1]+hi-lo+1)
        def restore(point): return point+prefix[bisect_right(anchors, point)]
        lifted = []
        for lo, hi, value in selected:
            check()
            cuts = sorted({lo, hi, *(a for a in anchors if lo < a < hi)})
            for first, last in zip(cuts, cuts[1:]): lifted.append((restore(first), restore(last-1)+1, value))
        selected = _coalesce(lifted+emitted, check)
    return selected


def verify_weighted_orbit_transversal(size, pairings, weight_intervals, certificate, *, dimension=None, check=None):
    """Bind each component weight to its least original label, not only a histogram."""
    poll = check if check is not None else lambda: None; poll()
    try:
        if type(certificate) is not dict or set(certificate) != {'schema', 'weighted_certificate', 'representative_runs'} or certificate['schema'] != 'weighted-orbit-transversal-v1': return False
        weighted = certificate['weighted_certificate']; source_pairs = list(pairings)
        if not verify_weighted_orbit_certificate(size, source_pairs, weight_intervals, weighted, dimension=dimension, check=poll): return False
        size = encoded_integer(size); dimension, runs = _initial_weights(size, weight_intervals, dimension, poll)
        proposed = certificate['representative_runs']
        if type(proposed) is not list: return False
        decoded = []
        for row in proposed:
            poll()
            if type(row) is not dict or set(row) != {'start', 'stop', 'weight'} or type(row['weight']) is not list or len(row['weight']) != dimension: return False
            try:
                lo, hi = encoded_integer(row['start']), encoded_integer(row['stop']); value = tuple(map(encoded_integer, row['weight']))
            except ValueError:
                return False
            if not 0 <= lo < hi <= size: return False
            if decoded and (lo < decoded[-1][1] or lo == decoded[-1][1] and value == decoded[-1][2]): return False
            decoded.append((lo, hi, value))
        actual = _reverse_tags(size, _canonical_pairings(size, source_pairs), runs, weighted['orbit_proof']['operations'], dimension, poll)
        return decoded == actual
    except _InvalidWeightedProof: return False
