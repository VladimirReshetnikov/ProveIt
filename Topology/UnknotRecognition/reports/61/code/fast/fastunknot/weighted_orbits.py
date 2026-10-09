"""Compressed additive weights for independently checked AHT orbit traces.

This implements the classical weighted extension of Agol--Hass--Thurston,
Section 6 (especially Lemma 15 and Theorem 16).  It is not a new orbit
algorithm.  The output groups equal orbit-weight vectors as
``(multiplicity, vector)`` and never expands integer points or individual
orbits.  Weights are signed integer vectors on half-open constant runs.

Every truncation first transfers the ENTIRE carrier range.  In particular,
periodic transfer folds that range into the first fundamental block and
zeros the entire range, even when only a short suffix is then removed.
Transferring only the removed suffix would not justify the classical
additive bound on the number of weight breakpoints.

The independent unweighted checker validates the input binding and every
local orbit relation before weighted replay begins.  This module does not
use or rerun the producer's scheduler during replay.  Its conclusion is an
orbit-weight multiset for the supplied interval system; a topology caller
must supply and justify its own weight construction.
"""

from bisect import bisect_left
from collections import Counter
from dataclasses import dataclass
from math import gcd
import re

from fastunknot.interval_orbit_verify import verify_orbit_certificate


class WeightedOrbitError(ValueError):
    """Invalid weight data, incompatible arguments, or an invalid orbit trace.

    Caller callbacks are never caught or converted to this exception.  A
    topology verifier can catch this type while allowing cancellation and
    deadline exceptions (including ordinary ValueError) to propagate.
    """


@dataclass(frozen=True, slots=True)
class WeightRun:
    """A constant vector on ``[start, stop)`` (validated by public APIs)."""

    start: int
    stop: int
    weight: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class WeightedOrbitResult:
    complete: bool
    orbits: int | None
    profiles: tuple[tuple[int, tuple[int, ...]], ...] | None
    dimension: int
    cycles: int | None
    stats: dict[str, int]
    certificate: dict | None = None


def _decode(value):
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+", value):
        return int(value, 16)
    raise WeightedOrbitError("Expected an integer or signed hexadecimal integer")


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise WeightedOrbitError(f"{name} must be a nonnegative integer")
    return value


def _append(runs, start, stop, vector):
    if start == stop:
        return
    if runs and runs[-1].stop == start and runs[-1].weight == vector:
        last = runs[-1]
        runs[-1] = WeightRun(last.start, stop, vector)
    else:
        runs.append(WeightRun(start, stop, vector))


def _weights(size, supplied, dimension, checkpoint):
    if dimension is not None and (type(dimension) is not int or dimension < 1):
        raise WeightedOrbitError("dimension must be a positive integer")
    result = []
    end = 0
    for raw in supplied:
        checkpoint()
        if isinstance(raw, WeightRun):
            start, stop, vector = raw.start, raw.stop, raw.weight
        elif isinstance(raw, (tuple, list)) and len(raw) == 3:
            start, stop, vector = raw
        else:
            raise WeightedOrbitError("Weights must be WeightRun objects or run triples")
        start = _natural(start, "run start")
        stop = _natural(stop, "run stop")
        if not start == end < stop <= size:
            raise WeightedOrbitError("Weight runs must partition [0, size) in order")
        if not isinstance(vector, (tuple, list)) or not vector:
            raise WeightedOrbitError("Every weight vector must be nonempty")
        if any(type(entry) is not int for entry in vector):
            raise WeightedOrbitError("Weight coordinates must be signed integers")
        vector = tuple(vector)
        if dimension is None:
            dimension = len(vector)
        if len(vector) != dimension:
            raise WeightedOrbitError("Weight vectors have inconsistent dimensions")
        _append(result, start, stop, vector)
        end = stop
    if end != size:
        raise WeightedOrbitError("Weight runs must cover the whole universe")
    return result, dimension if dimension is not None else 1


def _mass(runs, dimension, absolute=False):
    return tuple(sum((run.stop - run.start)
                     * (abs(run.weight[j]) if absolute else run.weight[j])
                     for run in runs) for j in range(dimension))


def _largest_bits(runs):
    return max((abs(value).bit_length() for run in runs for value in run.weight),
               default=0)


def _add_interval(events, start, stop, vector, multiplier=1):
    if start == stop or multiplier == 0:
        return
    for position, sign in ((start, multiplier), (stop, -multiplier)):
        delta = events.setdefault(position, [0] * len(vector))
        for j, value in enumerate(vector):
            delta[j] += sign * value


def _sweep(size, dimension, events, checkpoint):
    """Sum O(number of old runs) interval contributions by endpoints."""
    events.setdefault(0, [0] * dimension)
    events.setdefault(size, [0] * dimension)
    current = [0] * dimension
    previous = 0
    result = []
    for point in sorted(events):
        checkpoint()
        if not 0 <= point <= size:
            raise AssertionError("Weight contribution leaves the universe")
        _append(result, previous, point, tuple(current))
        for j, value in enumerate(events[point]):
            current[j] += value
        previous = point
    if any(current):
        raise AssertionError("Weight interval endpoint accounting failed")
    return result


def _transfer(runs, size, row, dimension, checkpoint):
    """Transfer [c,size) in full, retaining its zero band for accounting."""
    a, b, c, d, sign = row
    if d + 1 != size:
        raise AssertionError("Carrier must reach the end of the universe")
    periodic = sign == 1 and b >= c
    period = c - a
    events = {}
    for run in runs:
        checkpoint()
        # The entire old range is cleared; old weights below c are retained.
        if run.start < c:
            _add_interval(events, run.start, min(run.stop, c), run.weight)
        lo, hi = max(run.start, c), run.stop
        if lo >= hi:
            continue
        if periodic:
            quotient, remainder = divmod(hi - lo, period)
            _add_interval(events, a, c, run.weight, quotient)
            residue = a + (lo - a) % period
            first = min(remainder, c - residue)
            _add_interval(events, residue, residue + first, run.weight)
            _add_interval(events, a, a + remainder - first, run.weight)
        elif sign == 1:
            _add_interval(events, lo - period, hi - period, run.weight)
        else:
            total = a + d + 1
            _add_interval(events, total - hi, total - lo, run.weight)
    transferred = _sweep(size, dimension, events, checkpoint)
    # AHT Lemma 15: all internal range breakpoints disappear and relocate;
    # the fixed carrier/block boundaries add at most four constant bands.
    if len(transferred) > len(runs) + 4:
        raise AssertionError("Whole-range transfer exceeded the AHT band bound")
    return transferred, periodic


def _contract_weights(runs, gaps, emitted, checkpoint):
    """Emit static singleton orbits and compress remaining coordinates."""
    # The unweighted checker has already proved the gaps are exactly static.
    intervals = [(lo, hi + 1) for lo, hi in gaps]
    result = []
    gap_index = cursor = 0
    emitted_records = 0
    for run in runs:
        checkpoint()
        point = run.start
        while point < run.stop:
            checkpoint()
            while gap_index < len(intervals) and intervals[gap_index][1] <= point:
                gap_index += 1
            if gap_index == len(intervals) or point < intervals[gap_index][0]:
                end = min(run.stop, intervals[gap_index][0]) \
                    if gap_index < len(intervals) else run.stop
                length = end - point
                _append(result, cursor, cursor + length, run.weight)
                cursor += length
            else:
                end = min(run.stop, intervals[gap_index][1])
                emitted[run.weight] += end - point
                emitted_records += 1
            point = end
    if len(result) > len(runs):
        raise AssertionError("Contraction cannot introduce a weight breakpoint")
    return result, emitted_records


def _normalized(row):
    a, b, c, d, sign = row
    return [c, d, a, b, sign] if c < a else row


def _transmit_row(carrier, target, source_power, target_power):
    """Affine coordinate update; validity was proved by the trace checker."""
    a, b, c, d, sign = target

    def image(lo, hi, power):
        if power == 0:
            return lo, hi, 1
        if carrier[4] == 1:
            distance = power * (carrier[2] - carrier[0])
            return lo - distance, hi - distance, 1
        total = carrier[0] + carrier[3]
        return total - hi, total - lo, -1

    aa, bb, left_sign = image(a, b, source_power)
    cc, dd, right_sign = image(c, d, target_power)
    return _normalized([aa, bb, cc, dd, sign * left_sign * right_sign])


def _replay(size, pairings, runs, dimension, certificate, checkpoint,
            record_certificate):
    # Never infer local validity merely from the producer's own conclusion.
    if not verify_orbit_certificate(size, pairings, certificate, check=checkpoint):
        raise WeightedOrbitError("The unweighted orbit certificate is invalid")
    current = [[_decode(value) for value in row]
               for row in certificate["pairings"]]
    input_mass = _mass(runs, dimension)
    absolute_mass = _mass(runs, dimension, absolute=True)
    initial_runs = len(runs)
    stats = {"weight_initial_runs": initial_runs,
             "weight_peak_runs": initial_runs,
             "weight_transfers": 0,
             "weight_periodic_transfers": 0,
             "weight_isometric_transfers": 0,
             "weight_partial_truncations": 0,
             "weight_periodic_partial_truncations": 0,
             "weight_max_transfer_run_increase": 0,
             "weight_input_max_bits": _largest_bits(runs),
             "weight_peak_abs_bits": _largest_bits(runs),
             "weight_emission_records": 0,
             "weight_trace_operations": len(certificate["operations"])}
    emitted = Counter()
    for event in certificate["operations"]:
        checkpoint()
        operation = event["op"]
        if operation == "delete":
            del current[_decode(event["index"])]
        elif operation == "trim":
            i = _decode(event["index"])
            a, b, c, d, sign = current[i]
            last_left = (a + d - 1) // 2
            current[i] = [a, last_left, a + d - last_left, d, -1]
        elif operation == "merge":
            i, j = sorted((_decode(event["left"]), _decode(event["right"])))
            a, b, c, d, sign = current[i]
            aa, bb, cc, dd, ss = current[j]
            period = gcd(c - a, cc - aa)
            lo, hi = min(a, aa), max(d, dd)
            current[i] = [lo, hi - period, lo + period, hi, 1]
            del current[j]
        elif operation == "transmit":
            i, j = _decode(event["transmitter"]), _decode(event["target"])
            current[j] = _transmit_row(current[i], current[j],
                                       _decode(event["source_power"]),
                                       _decode(event["target_power"]))
        elif operation == "contract":
            gaps = [[_decode(value) for value in gap] for gap in event["gaps"]]
            runs, count = _contract_weights(runs, gaps, emitted, checkpoint)
            stats["weight_emission_records"] += count
            gap_ends = [hi for lo, hi in gaps]
            prefix = [0]
            for lo, hi in gaps:
                prefix.append(prefix[-1] + hi - lo + 1)

            def shifted(point):
                return point - prefix[bisect_left(gap_ends, point)]

            current = [[shifted(a), shifted(b), shifted(c), shifted(d), sign]
                       for a, b, c, d, sign in current]
            size -= prefix[-1]
        elif operation == "truncate":
            i, new_size = _decode(event["index"]), _decode(event["new_size"])
            a, b, c, d, sign = current[i]
            before = len(runs)
            runs, periodic = _transfer(runs, size, current[i], dimension, checkpoint)
            stats["weight_transfers"] += 1
            stats["weight_periodic_transfers" if periodic
                  else "weight_isometric_transfers"] += 1
            if new_size > c:
                stats["weight_partial_truncations"] += 1
                if periodic:
                    stats["weight_periodic_partial_truncations"] += 1
            stats["weight_max_transfer_run_increase"] = max(
                stats["weight_max_transfer_run_increase"], len(runs) - before)
            stats["weight_peak_runs"] = max(stats["weight_peak_runs"], len(runs))
            stats["weight_peak_abs_bits"] = max(stats["weight_peak_abs_bits"],
                                                _largest_bits(runs))
            retained = []
            for run in runs:
                checkpoint()
                if run.start >= new_size:
                    if any(run.weight):
                        raise AssertionError("Deleted range carries nonzero weight")
                    continue
                _append(retained, run.start, min(run.stop, new_size), run.weight)
            runs = retained
            removed = size - new_size
            if new_size == c:
                del current[i]
            elif sign == 1:
                current[i] = [a, b - removed, c, new_size - 1, 1]
            else:
                current[i] = [a + removed, b, c, new_size - 1, -1]
            size = new_size
        else:
            raise AssertionError("A validated trace has an unknown operation")
    if size or current or runs:
        raise AssertionError("A validated complete trace did not terminate")
    profiles = tuple((multiplicity, vector)
                     for vector, multiplicity in sorted(emitted.items()))
    orbit_count = sum(multiplicity for multiplicity, vector in profiles)
    if orbit_count != _decode(certificate["orbit_count"]):
        raise AssertionError("Weighted multiplicity differs from certified count")
    output_mass = tuple(sum(multiplicity * vector[j]
                            for multiplicity, vector in profiles)
                        for j in range(dimension))
    if output_mass != input_mass:
        raise AssertionError("Total vector weight was not conserved")
    if any(abs(vector[j]) > absolute_mass[j]
           for multiplicity, vector in profiles for j in range(dimension)):
        raise AssertionError("An output weight exceeds the absolute input mass")
    if stats["weight_peak_runs"] > initial_runs + 4 * stats["weight_transfers"]:
        raise AssertionError("The accumulated AHT band bound was violated")
    stats["weight_output_profiles"] = len(profiles)
    return WeightedOrbitResult(True, orbit_count, profiles, dimension, None,
                               stats, certificate if record_certificate else None)


def replay_weighted_orbit_profile(size, pairings, runs, certificate, *,
                                  dimension=None, check=None,
                                  record_certificate=False):
    """Validate and replay a supplied complete trace with additive weights.

    ``pairings`` uses the independent checker's accepted representations.
    ``runs`` is an ordered full partition of ``[0,size)`` by WeightRun values
    or ``(start, stop, vector)`` triples.  Adjacent equal weights are merged.
    Vectors have any common positive dimension and signed integer entries.
    For size zero, dimension defaults to one unless explicitly supplied.

    Invalid traces/weights raise WeightedOrbitError; callback exceptions propagate.
    The callback controls replay cancellation and deadlines.  ``cycles`` is
    None because a precomputed trace does not bind the producer's cycle count.
    Verification is polynomial in the supplied trace, not a containment
    promise for arbitrary untrusted input.  Callers may bound serialized size.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    _natural(size, "size")
    if type(record_certificate) is not bool:
        raise WeightedOrbitError("record_certificate must be bool")
    weights, dimension = _weights(size, runs, dimension, checkpoint)
    return _replay(size, list(pairings), weights, dimension, certificate,
                   checkpoint, record_certificate)


def weighted_orbit_profile(size, pairings, runs, *, max_cycles=None,
                           periodic_rule="fine_wilf", check=None,
                           record_certificate=False, certificate=None,
                           dimension=None):
    """Produce (or reuse), independently validate, and weight an AHT trace.

    ``max_cycles`` bounds the unweighted producer only.  The cooperative
    callback is shared by production, validation and weighted replay.  An
    incomplete producer result returns no orbit count and no partial profile.
    Passing a precomputed ``certificate`` avoids production and requires
    ``max_cycles=None``; the explicit replay entry point offers the same path.
    This wrapper uses the maintained default producer.  A different scheduler
    can supply any complete trace accepted by the independent checker.
    """
    if certificate is not None:
        if max_cycles is not None:
            raise WeightedOrbitError("A producer cycle cap cannot apply to a reused trace")
        return replay_weighted_orbit_profile(
            size, pairings, runs, certificate, dimension=dimension, check=check,
            record_certificate=record_certificate)
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    _natural(size, "size")
    if type(record_certificate) is not bool:
        raise WeightedOrbitError("record_certificate must be bool")
    weights, dimension = _weights(size, runs, dimension, checkpoint)
    pairings = list(pairings)
    from fastunknot.interval_orbits import count_orbits
    base = count_orbits(size, pairings, max_cycles=max_cycles,
                        periodic_rule=periodic_rule, check=checkpoint,
                        record_certificate=True)
    if not base.complete:
        return WeightedOrbitResult(False, None, None, dimension, base.cycles,
                                   dict(base.stats))
    result = _replay(size, pairings, weights, dimension, base.certificate,
                     checkpoint, record_certificate)
    stats = dict(base.stats)
    stats.update(result.stats)
    return WeightedOrbitResult(True, result.orbits, result.profiles, dimension,
                               base.cycles, stats, result.certificate)
