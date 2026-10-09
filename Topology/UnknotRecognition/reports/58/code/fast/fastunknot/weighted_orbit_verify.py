"""Independent verification of additive weights on certified interval orbits.

The maintained local-rule verifier validates the unweighted AHT trace.  This
module then replays weight transport independently of the weighted producer.
In particular, a translation fold is recovered from one residue-class sum
and its discrete derivative, rather than from quotient/remainder range adds.
No integer point or normal disc is expanded.
"""

from collections import defaultdict
from math import gcd
import re

from .interval_orbit_verify import verify_orbit_certificate


class _InvalidWeightedProof(ValueError):
    pass


def _integer(value):
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+", value):
        return int(value, 16)
    raise _InvalidWeightedProof("Expected an exact integer or hexadecimal string")


def _vector(value, dimension):
    if not isinstance(value, (list, tuple)) or len(value) != dimension:
        raise _InvalidWeightedProof("Weight-vector dimension differs")
    return tuple(_integer(entry) for entry in value)


def _add(left, right):
    return tuple(a + b for a, b in zip(left, right))


def _neg(value):
    return tuple(-entry for entry in value)


def _scale(value, multiplier):
    return tuple(multiplier * entry for entry in value)


def _event(events, point, increment, dimension):
    events[point] = _add(events.get(point, (0,) * dimension), increment)


def _append(runs, lo, hi, value):
    if lo == hi:
        return
    if runs and runs[-1][1] == lo and runs[-1][2] == value:
        runs[-1] = (runs[-1][0], hi, value)
    else:
        runs.append((lo, hi, value))


def _integrate(events, size, dimension, poll):
    """Integrate an integer-valued jump measure on a finite interval."""
    if size == 0:
        return []
    result, value = [], (0,) * dimension
    points = sorted(set(events) | {0, size})
    for lo, hi in zip(points, points[1:]):
        poll()
        if not 0 <= lo <= hi <= size:
            raise _InvalidWeightedProof("Weight jumps leave the current universe")
        value = _add(value, events.get(lo, (0,) * dimension))
        _append(result, lo, hi, value)
    if _add(value, events.get(size, (0,) * dimension)) != (0,) * dimension:
        raise _InvalidWeightedProof("A finite weight function has nonzero final jump")
    return result


def _initial_weights(size, intervals, dimension, poll):
    if not isinstance(intervals, (list, tuple)):
        raise _InvalidWeightedProof("Weight intervals must be an explicit sequence")
    if dimension is None:
        if intervals:
            first = intervals[0]
            if (not isinstance(first, (list, tuple)) or len(first) != 3
                    or not isinstance(first[2], (list, tuple))):
                raise _InvalidWeightedProof("Malformed additive weight interval")
            dimension = len(first[2])
        else:
            dimension = 1
    dimension = _integer(dimension)
    if dimension < 1:
        raise _InvalidWeightedProof("Weight dimension must be positive")
    events = {}
    for interval in intervals:
        poll()
        if not isinstance(interval, (list, tuple)) or len(interval) != 3:
            raise _InvalidWeightedProof("Malformed additive weight interval")
        lo, hi = _integer(interval[0]), _integer(interval[1])
        value = _vector(interval[2], dimension)
        if not 0 <= lo <= hi <= size:
            raise _InvalidWeightedProof("Initial weight interval leaves the universe")
        _event(events, lo, value, dimension)
        _event(events, hi, _neg(value), dimension)
    return dimension, _integrate(events, size, dimension, poll)


def _canonical_pairings(size, pairings):
    """Decode only after the independent local-rule checker has accepted."""
    result = []
    for raw in pairings:
        if isinstance(raw, dict):
            start, stop, sign, offset = (_integer(raw[name]) for name in
                                         ("start", "stop", "sign", "offset"))
            if start == stop:
                continue
            c, d = sorted((sign * start + offset, sign * (stop - 1) + offset))
            row = [start, stop - 1, c, d, sign]
        elif isinstance(raw, (list, tuple)):
            row = [_integer(value) for value in raw]
        else:
            row = [raw.a, raw.b, raw.c, raw.d, -1 if raw.reverse else 1]
        if row[2] < row[0]:
            row = [row[2], row[3], row[0], row[1], row[4]]
        result.append(row)
    return result


def _prefix_events(runs, cut, dimension, poll):
    events = {}
    for lo, hi, value in runs:
        poll()
        if lo >= cut:
            break
        hi = min(hi, cut)
        _event(events, lo, value, dimension)
        _event(events, hi, _neg(value), dimension)
    return events


def _translation_fold(runs, size, cut, period, dimension, poll):
    """Fold a suffix using a residue anchor and a discrete derivative.

    Extend suffix weights by zero to Z and write Delta w(x)=w(x)-w(x-1).
    For F(r)=sum_{x == r (mod period)} w(x), one has
    Delta F(r)=sum_{x == r (mod period)} Delta w(x).
    One arithmetic-progression count fixes F at the leftmost retained residue;
    integration of these mapped jumps fixes every other residue exactly.
    """
    bottom = cut - period
    if not 0 <= bottom < cut < size:
        raise _InvalidWeightedProof("Invalid translation weight fold")
    events = _prefix_events(runs, cut, dimension, poll)
    mapped, anchor = {}, (0,) * dimension
    for lo, hi, value in runs:
        poll()
        lo = max(lo, cut)
        if lo >= hi:
            continue
        multiplicity = ((hi - 1 - bottom) // period
                        - (lo - 1 - bottom) // period)
        anchor = _add(anchor, _scale(value, multiplicity))
        left = bottom + (lo - bottom) % period
        right = bottom + (hi - bottom) % period
        _event(mapped, left, value, dimension)
        _event(mapped, right, _neg(value), dimension)
    _event(events, bottom, anchor, dimension)
    last = anchor
    for point in sorted(mapped):
        poll()
        if point != bottom:
            _event(events, point, mapped[point], dimension)
            last = _add(last, mapped[point])
    _event(events, cut, _neg(last), dimension)
    return _integrate(events, cut, dimension, poll)


def _reflection_fold(runs, size, cut, centre, dimension, poll):
    """Reflect suffix jumps with reversed sign, then integrate."""
    events = _prefix_events(runs, cut, dimension, poll)
    for lo, hi, value in runs:
        poll()
        lo = max(lo, cut)
        if lo >= hi:
            continue
        # Integer reflection x -> centre-x sends [lo,hi) to
        # [centre-hi+1, centre-lo+1). The +1 belongs to half-open indexing.
        left, right = centre - hi + 1, centre - lo + 1
        if not 0 <= left < right <= cut:
            raise _InvalidWeightedProof("Reflected suffix leaves the retained universe")
        _event(events, left, value, dimension)
        _event(events, right, _neg(value), dimension)
    return _integrate(events, cut, dimension, poll)


def _contract_weights(runs, size, gaps, histogram, poll):
    """Remove static intervals and record one final orbit per removed point."""
    breaks = {0, size}
    for lo, hi, _ in runs:
        breaks.update((lo, hi))
    for lo, hi in gaps:
        breaks.update((lo, hi + 1))
    points = sorted(breaks)
    out, run_index, gap_index, removed = [], 0, 0, 0
    for lo, hi in zip(points, points[1:]):
        poll()
        while runs[run_index][1] <= lo:
            run_index += 1
        while gap_index < len(gaps) and gaps[gap_index][1] < lo:
            gap_index += 1
        value = runs[run_index][2]
        inside = gap_index < len(gaps) and gaps[gap_index][0] <= lo
        if inside:
            histogram[value] += hi - lo
            removed += hi - lo
        else:
            _append(out, lo - removed, hi - removed, value)
    return out, size - removed


def _move_interval(lo, hi, carrier, power):
    if power == 0:
        return lo, hi, 1
    a, _, c, d, sign = carrier
    if sign == 1:
        offset = power * (c - a)
        return lo - offset, hi - offset, 1
    return a + d - hi, a + d - lo, -1


def _replay(size, pairs, runs, trace, dimension, poll):
    histogram = defaultdict(int)
    for event in trace:
        poll()
        kind = event["op"]
        if kind == "delete":
            del pairs[_integer(event["index"])]
        elif kind == "trim":
            index = _integer(event["index"])
            a, _, _, d, _ = pairs[index]
            endpoint = (a + d - 1) // 2
            pairs[index] = [a, endpoint, a + d - endpoint, d, -1]
        elif kind == "merge":
            i, j = sorted((_integer(event["left"]), _integer(event["right"])))
            a, b, c, d, _ = pairs[i]
            aa, bb, cc, dd, _ = pairs[j]
            period = gcd(c - a, cc - aa)
            low, high = min(a, aa), max(d, dd)
            pairs[i] = [low, high - period, low + period, high, 1]
            del pairs[j]
        elif kind == "transmit":
            carrier = pairs[_integer(event["transmitter"])]
            target = _integer(event["target"])
            a, b, c, d, sign = pairs[target]
            a, b, left_sign = _move_interval(
                a, b, carrier, _integer(event["source_power"]))
            c, d, right_sign = _move_interval(
                c, d, carrier, _integer(event["target_power"]))
            if c < a:
                a, b, c, d = c, d, a, b
            pairs[target] = [a, b, c, d, sign * left_sign * right_sign]
        elif kind == "contract":
            gaps = [[_integer(x) for x in gap] for gap in event["gaps"]]
            runs, size = _contract_weights(runs, size, gaps, histogram, poll)

            def shift(point):
                return point - sum(hi - lo + 1 for lo, hi in gaps if hi < point)

            pairs = [[shift(a), shift(b), shift(c), shift(d), sign]
                     for a, b, c, d, sign in pairs]
        elif kind == "truncate":
            index = _integer(event["index"])
            cut = _integer(event["new_size"])
            a, b, c, d, sign = pairs[index]
            if sign == 1:
                runs = _translation_fold(runs, size, cut, c - a, dimension, poll)
            else:
                runs = _reflection_fold(runs, size, cut, a + d, dimension, poll)
            removed = size - cut
            if cut == c:
                del pairs[index]
            elif sign == 1:
                pairs[index] = [a, b - removed, c, cut - 1, 1]
            else:
                pairs[index] = [a + removed, b, c, cut - 1, -1]
            size = cut
        else:
            raise _InvalidWeightedProof("Unknown checked orbit operation")
    if size != 0 or pairs or runs:
        raise _InvalidWeightedProof("Weighted trace did not finish")
    return dict(histogram)


def verify_weighted_orbit_certificate(size, pairings, weight_intervals, certificate,
                                      *, dimension=None, check=None):
    """Verify exact component-weight sums without calling a weighted producer.

    Initial weights are additive half-open intervals (lo,hi,integer-vector).
    The supplied certificate must bind the same canonical weight function and
    the same pairing list. Invalid proofs return False. Cooperative callback
    exceptions propagate. Work depends polynomially on the explicit source,
    trace and endpoint bit lengths, never on the number of represented points.
    """
    poll = check if check is not None else lambda: None
    try:
        poll()
        size = _integer(size)
        if size < 0 or not isinstance(certificate, dict):
            return False
        expected = {"schema", "size", "dimension", "weights", "orbit_proof", "histogram"}
        if (set(certificate) != expected
                or certificate["schema"] != "weighted-interval-orbits-v1"
                or _integer(certificate["size"]) != size):
            return False
        dimension, runs = _initial_weights(size, weight_intervals, dimension, poll)
        if _integer(certificate["dimension"]) != dimension:
            return False
        supplied = certificate["weights"]
        if not isinstance(supplied, list):
            return False
        decoded = []
        for row in supplied:
            poll()
            if not isinstance(row, (list, tuple)) or len(row) != 3:
                return False
            decoded.append((_integer(row[0]), _integer(row[1]),
                            _vector(row[2], dimension)))
        if decoded != runs:
            return False
        proof = certificate["orbit_proof"]
        if not verify_orbit_certificate(size, pairings, proof, check=poll):
            return False
        pairs = _canonical_pairings(size, pairings)
        actual = _replay(size, pairs, runs, proof["operations"], dimension, poll)
        supplied = certificate["histogram"]
        if not isinstance(supplied, list):
            return False
        claimed, previous = {}, None
        for row in supplied:
            poll()
            if not isinstance(row, dict) or set(row) != {"weight", "orbits"}:
                return False
            value = _vector(row["weight"], dimension)
            count = _integer(row["orbits"])
            if count < 1 or (previous is not None and value <= previous):
                return False
            claimed[value], previous = count, value
        if claimed != actual or sum(actual.values()) != _integer(proof["orbit_count"]):
            return False
        # An independently cheap conservation identity also covers signed values.
        original_mass = (0,) * dimension
        for lo, hi, value in runs:
            original_mass = _add(original_mass, _scale(value, hi - lo))
        final_mass = (0,) * dimension
        for value, count in actual.items():
            final_mass = _add(final_mass, _scale(value, count))
        poll()
        return original_mass == final_mass
    except _InvalidWeightedProof:
        return False
