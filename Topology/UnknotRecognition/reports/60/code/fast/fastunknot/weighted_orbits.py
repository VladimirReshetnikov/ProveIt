"""Weighted AHT orbit sums over the maintained, independently checked trace.

This implements the classical Agol--Hass--Thurston weight extension.  It
does not introduce another orbit scheduler.  Only full-range weight folding
before truncation and output of static points extend the six existing rules.

Input weight intervals are half-open and additive.  Their vectors may have
negative entries.  All arithmetic uses binary integers; no represented point
or orbit is expanded.  Output groups orbits by their exact weight vector.
The optional certificate is independently replayable without orbit search;
its weight arithmetic is shared with production and is cross-checked by the
literal graph oracle in the tests.  It is not a knot certificate.
"""

from dataclasses import dataclass
from math import gcd

from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import (
    _integer as _decoded_integer,
    _public_pairings,
    _transmitted_row,
    verify_orbit_certificate,
)


def _nat(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f'{name} must be a nonnegative integer')
    return value


@dataclass(frozen=True, slots=True)
class WeightInterval:
    start: int
    stop: int
    value: tuple[int, ...]

    def __post_init__(self):
        _nat(self.start, 'start')
        _nat(self.stop, 'stop')
        if self.stop <= self.start:
            raise ValueError('weight intervals must be nonempty and half-open')
        if (type(self.value) is not tuple
                or any(type(x) is not int for x in self.value)):
            raise ValueError('a weight value must be an integer tuple')


@dataclass(frozen=True, slots=True)
class WeightedOrbitClass:
    value: tuple[int, ...]
    multiplicity: int


@dataclass(frozen=True, slots=True)
class WeightedOrbitResult:
    complete: bool
    orbits: int | None
    classes: tuple[WeightedOrbitClass, ...] | None
    aggregate: tuple[int, ...] | None
    cycles: int
    stats: dict
    certificate: dict | None = None
    reason: str | None = None


class _CapacityReached(Exception):
    pass


def _add_value(first, second):
    return tuple(a + b for a, b in zip(first, second))


def _scale(value, multiplier):
    return tuple(multiplier * v for v in value)


def _canonical(size, contributions, dimension, check):
    """Sweep additive half-open weighted intervals into a complete partition."""
    zero = (0,) * dimension
    events = {0: zero, size: zero}
    for lo, hi, value in contributions:
        check()
        if lo == hi or not any(value):
            continue
        events[lo] = _add_value(events.get(lo, zero), value)
        events[hi] = _add_value(events.get(hi, zero), _scale(value, -1))
    result, value, previous = [], zero, 0
    for point in sorted(events):
        check()
        if point > previous:
            if result and result[-1][2] == value:
                result[-1] = (result[-1][0], point, value)
            else:
                result.append((previous, point, value))
        value = _add_value(value, events[point])
        previous = point
    if value != zero or previous != size:
        raise ArithmeticError('weight partition endpoints do not balance')
    return result


def _input_weights(size, weights, dimension, check):
    _nat(size, 'size')
    if type(dimension) is not int or dimension < 0:
        raise ValueError('dimension must be a nonnegative integer')
    contributions = []
    for weight in weights:
        check()
        if not isinstance(weight, WeightInterval):
            raise ValueError('weights must contain WeightInterval values')
        if weight.stop > size or len(weight.value) != dimension:
            raise ValueError('weight interval outside universe or wrong dimension')
        contributions.append((weight.start, weight.stop, weight.value))
    return _canonical(size, contributions, dimension, check)


def _aggregate(blocks, dimension):
    result = [0] * dimension
    for lo, hi, value in blocks:
        for j, coordinate in enumerate(value):
            result[j] += (hi - lo) * coordinate
    return tuple(result)


def _fold(blocks, carrier, size, new_size, dimension, check):
    """Push the ENTIRE carrier range to [a,c), then remove a zero suffix.

    For a positive carrier, rho(x)=a+(x-a) mod(c-a).  A block of
    length qp+r gives q copies everywhere on [a,c) and one on its
    cyclic residual interval.  A trimmed reflection uses one inverse.
    Folding only the actually deleted suffix is deliberately not used:
    full-range folding is what gives the additive breakpoint bound.
    """
    a, b, c, d, sign = carrier
    contributions = []
    for lo, hi, value in blocks:
        check()
        if lo < c:
            contributions.append((lo, min(hi, c), value))
        lo = max(lo, c)
        if lo >= hi:
            continue
        if sign == -1:
            if b >= c:
                raise ArithmeticError('weight folding needs a trimmed reflection')
            contributions.append((a + d - hi + 1, a + d - lo + 1, value))
            continue
        period = c - a
        if period <= 0:
            raise ArithmeticError('weight folding needs a positive translation')
        quotient, remainder = divmod(hi - lo, period)
        if quotient:
            contributions.append((a, c, _scale(value, quotient)))
        if remainder:
            first = a + (lo - a) % period
            stop = first + remainder
            contributions.append((first, min(stop, c), value))
            if stop > c:
                contributions.append((a, a + stop - c, value))
    return _canonical(new_size, contributions, dimension, check)


def _contract_weights(blocks, gaps, size, dimension, emitted, check):
    """Emit each removed static point with its final weight and close gaps."""
    contributions = []
    # Each disjoint kept/gap interval is intersected by a linear merge scan.
    cells, cursor, removed = [], 0, 0
    for lo, hi in gaps:
        check()
        if cursor < lo:
            cells.append((cursor, lo, False, removed))
        cells.append((lo, hi + 1, True, removed))
        removed += hi - lo + 1
        cursor = hi + 1
    if cursor < size:
        cells.append((cursor, size, False, removed))
    i = j = 0
    while i < len(blocks) and j < len(cells):
        check()
        a, b, value = blocks[i]
        c, d, static, shift = cells[j]
        lo, hi = max(a, c), min(b, d)
        if lo < hi:
            if static:
                emitted[value] = emitted.get(value, 0) + hi - lo
            else:
                contributions.append((lo - shift, hi - shift, value))
        if b <= d:
            i += 1
        if d <= b:
            j += 1
    return _canonical(size - removed, contributions, dimension, check)


def _replay_weights(size, pairings, initial, dimension, trace, check, limits):
    """Transport weights along an already independently validated trace."""
    current = _public_pairings(size, pairings)
    blocks, emitted = initial, {}
    stats = {'initial_weight_blocks': len(initial),
             'peak_weight_blocks': len(initial), 'weight_transfers': 0,
             'max_transfer_block_growth': 0, 'replayed_events': 0,
             'output_records': 0,
             'peak_weight_bits': max((abs(x).bit_length() for _, _, v in initial
                                      for x in v), default=0)}

    def capacity():
        stats['peak_weight_blocks'] = max(stats['peak_weight_blocks'], len(blocks))
        stats['output_records'] = len(emitted)
        stats['peak_weight_bits'] = max(
            stats['peak_weight_bits'],
            max((abs(x).bit_length() for _, _, v in blocks for x in v), default=0))
        if limits[0] is not None and len(blocks) > limits[0]:
            raise _CapacityReached('weight_block_limit')
        if limits[1] is not None and len(emitted) > limits[1]:
            raise _CapacityReached('output_record_limit')

    try:
        capacity()
        for event in trace['operations']:
            check()
            if limits[2] is not None and stats['replayed_events'] >= limits[2]:
                raise _CapacityReached('replay_event_limit')
            op = event['op']
            if op == 'delete':
                del current[_decoded_integer(event['index'])]
            elif op == 'trim':
                i = _decoded_integer(event['index'])
                a, b, c, d, sign = current[i]
                current[i] = [a, (a + d - 1) // 2, (a + d) // 2 + 1, d, -1]
            elif op == 'merge':
                i, j = sorted((_decoded_integer(event['left']),
                               _decoded_integer(event['right'])))
                a, b, c, d, _ = current[i]
                aa, bb, cc, dd, _ = current[j]
                period = gcd(c - a, cc - aa)
                lo, hi = min(a, aa), max(d, dd)
                current[i] = [lo, hi - period, lo + period, hi, 1]
                del current[j]
            elif op == 'transmit':
                i = _decoded_integer(event['transmitter'])
                j = _decoded_integer(event['target'])
                current[j] = _transmitted_row(current[i], current[j],
                    event['source_power'], event['target_power'], size)
            elif op == 'contract':
                gaps = [[_decoded_integer(lo), _decoded_integer(hi)]
                        for lo, hi in event['gaps']]
                blocks = _contract_weights(blocks, gaps, size, dimension,
                                            emitted, check)
                def shifted(point):
                    return point - sum(hi - lo + 1 for lo, hi in gaps if hi < point)
                current = [[shifted(a), shifted(b), shifted(c), shifted(d), sign]
                           for a, b, c, d, sign in current]
                size -= sum(hi - lo + 1 for lo, hi in gaps)
            elif op == 'truncate':
                i = _decoded_integer(event['index'])
                new_size = _decoded_integer(event['new_size'])
                carrier = current[i]
                old_count = len(blocks)
                blocks = _fold(blocks, carrier, size, new_size, dimension, check)
                stats['weight_transfers'] += 1
                growth = len(blocks) - old_count
                stats['max_transfer_block_growth'] = max(
                    stats['max_transfer_block_growth'], growth)
                if growth > 3:
                    raise ArithmeticError('rightmost-carrier three-run bound failed')
                a, b, c, d, sign = carrier
                if new_size == c:
                    del current[i]
                elif sign == 1:
                    current[i] = [a, b - (size - new_size), c, new_size - 1, sign]
                else:
                    current[i] = [a + size - new_size, b, c, new_size - 1, sign]
                size = new_size
            else:
                raise ArithmeticError('unexpected independently validated operation')
            stats['replayed_events'] += 1
            capacity()
    except _CapacityReached as error:
        return None, stats, str(error)
    if size or current or blocks:
        raise ArithmeticError('weighted trace did not terminate')
    result = tuple(WeightedOrbitClass(value, count)
                   for value, count in sorted(emitted.items()))
    return result, stats, None


def weighted_orbit_counts(size, pairings, weights, *, dimension,
                          max_cycles=None, periodic_rule='fine_wilf', check=None,
                          max_weight_blocks=None, max_output_records=None,
                          max_operations=None,
                          record_certificate=False):
    """Return exact orbit-weight vectors with compressed multiplicities.

    max_cycles belongs to the unchanged orbit scheduler.  The other optional
    limits cap canonical current weight blocks, distinct output records, and
    replayed events.  They are cooperative resource limits, not memory or
    elapsed-time guarantees.  Exhaustion returns no counts, sums, or proof.
    check() exceptions propagate during validation, search and replay.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be boolean')
    for limit, label in ((max_weight_blocks, 'max_weight_blocks'),
                         (max_output_records, 'max_output_records'),
                         (max_operations, 'max_operations')):
        if limit is not None:
            _nat(limit, label)
    initial = _input_weights(size, weights, dimension, checkpoint)
    pairings = list(pairings)
    orbit = count_orbits(size, pairings, max_cycles=max_cycles,
                         periodic_rule=periodic_rule, check=checkpoint,
                         record_certificate=True)
    if not orbit.complete:
        return WeightedOrbitResult(False, None, None, None, orbit.cycles,
                                   {'orbit': orbit.stats}, reason='cycle_limit')
    trace = orbit.certificate
    if not verify_orbit_certificate(size, pairings, trace, check=checkpoint):
        raise ArithmeticError('the orbit producer emitted an invalid trace')
    result, stats, reason = _replay_weights(size, pairings, initial, dimension,
        trace, checkpoint, (max_weight_blocks, max_output_records, max_operations))
    stats['orbit'] = orbit.stats
    if result is None:
        return WeightedOrbitResult(False, None, None, None, orbit.cycles, stats,
                                   reason=reason)
    if sum(row.multiplicity for row in result) != orbit.orbits:
        raise ArithmeticError('orbit multiplicities do not match the checked count')
    aggregate = tuple(sum(row.multiplicity * row.value[j] for row in result)
                      for j in range(dimension))
    if aggregate != _aggregate(initial, dimension):
        raise ArithmeticError('weighted transport did not conserve total weight')
    certificate = None
    if record_certificate:
        certificate = {'version': 1, 'dimension': dimension,
                       'weights': [[lo, hi, list(value)] for lo, hi, value in initial],
                       'classes': [[list(row.value), row.multiplicity] for row in result],
                       'orbit_certificate': trace}
    return WeightedOrbitResult(True, orbit.orbits, result, aggregate,
                               orbit.cycles, stats, certificate)


def replay_weighted_orbits(size, pairings, weights, orbit_certificate, *,
                           dimension, check=None, max_weight_blocks=None,
                           max_output_records=None, max_operations=None):
    """Derive component weights from a supplied unweighted orbit trace.

    No orbit scheduler is called. Invalid traces return an incomplete result
    with reason 'invalid_orbit_certificate'. Cooperative capacity exhaustion
    also returns no mathematical output. cycles is zero: a local proof does
    not authenticate or prescribe the scheduler's cycles.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    for limit, label in ((max_weight_blocks, 'max_weight_blocks'),
                         (max_output_records, 'max_output_records'),
                         (max_operations, 'max_operations')):
        if limit is not None:
            _nat(limit, label)
    initial = _input_weights(size, weights, dimension, checkpoint)
    pairings = list(pairings)
    if (max_operations is not None and type(orbit_certificate) is dict
            and type(orbit_certificate.get('operations')) is list
            and len(orbit_certificate['operations']) > max_operations):
        return WeightedOrbitResult(False, None, None, None, 0, {},
                                   reason='replay_event_limit')
    if not verify_orbit_certificate(size, pairings, orbit_certificate,
                                     check=checkpoint):
        return WeightedOrbitResult(False, None, None, None, 0, {},
                                   reason='invalid_orbit_certificate')
    result, stats, reason = _replay_weights(size, pairings, initial, dimension,
        orbit_certificate, checkpoint,
        (max_weight_blocks, max_output_records, max_operations))
    if result is None:
        return WeightedOrbitResult(False, None, None, None, 0, stats, reason=reason)
    aggregate = tuple(sum(row.multiplicity * row.value[j] for row in result)
                      for j in range(dimension))
    orbits = sum(row.multiplicity for row in result)
    if (aggregate != _aggregate(initial, dimension)
            or orbits != _decoded_integer(orbit_certificate['orbit_count'])):
        raise ArithmeticError('weighted replay conservation failed')
    return WeightedOrbitResult(True, orbits, result, aggregate, 0, stats)


def verify_weighted_orbit_certificate(size, pairings, weights, certificate, *,
                                      dimension, check=None,
                                      max_weight_blocks=None,
                                      max_output_records=None,
                                      max_operations=None):
    """Check a weight result using local replay, without invoking orbit search.

    The orbit trace, normalized additive input weights, and output classes
    must all bind exactly to the caller's input.  Malformed/over-limit data
    returns False.  User cancellation exceptions are not swallowed.
    """
    checkpoint = check if check is not None else lambda: None
    checkpoint()
    for limit, label in ((max_weight_blocks, 'max_weight_blocks'),
                         (max_output_records, 'max_output_records'),
                         (max_operations, 'max_operations')):
        if limit is not None:
            _nat(limit, label)
    initial = _input_weights(size, weights, dimension, checkpoint)
    pairings = list(pairings)
    # Restrict exception handling to schema decoding. Callback exceptions
    # propagate even if their class happens to derive from ValueError.
    try:
        if (type(certificate) is not dict or set(certificate) != {
                'version', 'dimension', 'weights', 'classes', 'orbit_certificate'}
                or _decoded_integer(certificate['version']) != 1
                or _decoded_integer(certificate['dimension']) != dimension
                or type(certificate['weights']) is not list
                or type(certificate['classes']) is not list):
            return False
    except (ValueError, TypeError, KeyError):
        return False
    bound_weights = []
    for row in certificate['weights']:
        checkpoint()
        try:
            if (type(row) is not list or len(row) != 3 or type(row[2]) is not list
                    or len(row[2]) != dimension):
                return False
            lo, hi = _decoded_integer(row[0]), _decoded_integer(row[1])
            value = tuple(_decoded_integer(x) for x in row[2])
            bound_weights.append((lo, hi, value))
        except (ValueError, TypeError, KeyError):
            return False
    claimed = []
    for row in certificate['classes']:
        checkpoint()
        try:
            if (type(row) is not list or len(row) != 2 or type(row[0]) is not list
                    or len(row[0]) != dimension):
                return False
            value = tuple(_decoded_integer(x) for x in row[0])
            count = _decoded_integer(row[1])
            if len(value) != dimension or count <= 0:
                return False
            claimed.append(WeightedOrbitClass(value, count))
        except (ValueError, TypeError, KeyError):
            return False
    if bound_weights != initial:
        return False
    trace = certificate['orbit_certificate']
    if (max_operations is not None and type(trace) is dict
            and type(trace.get('operations')) is list
            and len(trace['operations']) > max_operations):
        return False
    if not verify_orbit_certificate(size, pairings, trace, check=checkpoint):
        return False
    result, _, _ = _replay_weights(size, pairings, initial, dimension, trace,
        checkpoint, (max_weight_blocks, max_output_records, max_operations))
    return result is not None and result == tuple(claimed)
