"""Compile a verified binary interval-orbit trace into exact point queries.

This module is additive to fastunknot: the existing producer and independent
trace checker are unchanged.  A prepared index maps each source point to the
minimum original point of its orbit.  Preparation and queries never enumerate
the represented interval.  Ordinal labels follow trace emission order and are
not canonical; minimum representatives are canonical across valid traces.
"""

from bisect import bisect_right
from copy import deepcopy
from dataclasses import dataclass
from math import gcd

from fastunknot.integer_codec import encoded_integer
from fastunknot.interval_orbit_verify import (
    _public_pairings, _transmitted_row, verify_orbit_certificate,
)


def _number(value, name, lower=0):
    try:
        value = encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f'{name} must be an integer or hexadecimal string') from exc
    if value < lower:
        raise ValueError(f'{name} must be at least {lower}')
    return value


def _poll(check):
    if check is not None:
        check()


def _minimum_ranges(contractions, count, check):
    """Lift static gaps to source hulls and form the canonical minimum set.

    Between the source images of a current gap's endpoints, the only missing
    original points are minima emitted by previous contractions.  Points
    removed by earlier suffix truncations lie beyond the current live prefix.
    Thus adjoining the entire source hull adds exactly new minima, possibly
    joining old minimum intervals.  There is at most one hull per static gap.
    """
    hulls = []
    inverse_steps = 0
    for position, contraction in enumerate(contractions):
        _poll(check)
        earlier = contractions[:position]
        for lo, stop in zip(contraction.starts, contraction.stops):
            _poll(check)
            hi = stop - 1
            for old in reversed(earlier):
                _poll(check)
                lo, hi = old.backward(lo), old.backward(hi)
                inverse_steps += 2
            hulls.append((lo, hi + 1))
    ranges = []
    for lo, stop in sorted(hulls):
        _poll(check)
        if ranges and lo <= ranges[-1][1]:
            ranges[-1] = (ranges[-1][0], max(ranges[-1][1], stop))
        else:
            ranges.append((lo, stop))
    prefix = [0]
    for lo, stop in ranges:
        prefix.append(prefix[-1] + stop - lo)
    if prefix[-1] != count:
        raise ArithmeticError('minimum source intervals disagree with the orbit count')
    return (tuple(ranges), tuple(lo for lo, _ in ranges), tuple(prefix), inverse_steps)


@dataclass(frozen=True, slots=True)
class _Contraction:
    starts: tuple
    stops: tuple
    prefix: tuple
    collapsed: tuple
    first_orbit: int
    position: int

    @classmethod
    def from_gaps(cls, gaps, first_orbit, position):
        starts, stops, prefix, collapsed = [], [], [0], []
        for lo, hi in gaps:
            starts.append(lo)
            stops.append(hi + 1)
            collapsed.append(lo - prefix[-1])
            prefix.append(prefix[-1] + hi - lo + 1)
        return cls(tuple(starts), tuple(stops), tuple(prefix),
                   tuple(collapsed), first_orbit, position)

    @property
    def emitted(self):
        return self.prefix[-1]

    def forward(self, point):
        i = bisect_right(self.starts, point) - 1
        if i >= 0 and point < self.stops[i]:
            return None, self.first_orbit + self.prefix[i] + point - self.starts[i]
        removed = self.prefix[bisect_right(self.stops, point)]
        return point - removed, None

    def backward(self, point):
        # This is the order-preserving inverse on surviving points.  Adjacent
        # gaps, if supplied by another valid schema, are also handled by <=.
        return point + self.prefix[bisect_right(self.collapsed, point)]

    def emitted_point(self, ordinal):
        offset = ordinal - self.first_orbit
        i = bisect_right(self.prefix, offset) - 1
        return self.starts[i] + offset - self.prefix[i]


@dataclass(frozen=True, slots=True)
class _Truncation:
    cut: int
    period: int
    reflection_sum: int | None

    def forward(self, point):
        if point < self.cut:
            return point
        if self.reflection_sum is not None:
            return self.reflection_sum - point
        base = self.cut - self.period
        return base + (point - base) % self.period


@dataclass(frozen=True, slots=True)
class OrbitLocation:
    representative: int
    ordinal: int
    forward_steps: int
    reverse_contractions: int


@dataclass(frozen=True, slots=True)
class OrbitIndex:
    size: int
    count: int
    _steps: tuple
    _contractions: tuple
    _emission_starts: tuple
    _event_count: int
    _gap_count: int
    _max_gap_count: int
    _minimum_intervals: tuple
    _minimum_starts: tuple
    _minimum_prefix: tuple
    _minimum_inverse_steps: int

    @classmethod
    def from_certificate(cls, size, pairings, certificate, check=None):
        """Verify a complete source-bound trace and compile an immutable index.

        The checker is the maintained independent checker, not count_orbits.
        Copying supplied proof data prevents later caller mutation from
        changing the prepared index.  A malformed or incomplete proof raises
        ValueError; caller cancellation propagates.
        """
        _poll(check)
        size = _number(size, 'size')
        proof = deepcopy(certificate)
        supplied = deepcopy(list(pairings))
        if not verify_orbit_certificate(size, supplied, proof, check=check):
            raise ValueError('a complete source-bound orbit certificate is required')
        rows = _public_pairings(size, supplied)
        initial_size = size
        steps, contractions, emission_starts = [], [], []
        emitted = gap_count = max_gap_count = 0
        for event in proof['operations']:
            _poll(check)
            op = event['op']
            if op == 'delete':
                rows.pop(encoded_integer(event['index']))
            elif op == 'trim':
                i = encoded_integer(event['index'])
                a, _, _, d, _ = rows[i]
                b = (a + d - 1) // 2
                rows[i] = [a, b, a + d - b, d, -1]
            elif op == 'merge':
                i, j = sorted((encoded_integer(event['left']),
                               encoded_integer(event['right'])))
                a, _, c, d, _ = rows[i]
                aa, _, cc, dd, _ = rows[j]
                period = gcd(c - a, cc - aa)
                lo, hi = min(a, aa), max(d, dd)
                rows[i] = [lo, hi - period, lo + period, hi, 1]
                rows.pop(j)
            elif op == 'transmit':
                i = encoded_integer(event['transmitter'])
                j = encoded_integer(event['target'])
                rows[j] = _transmitted_row(rows[i], rows[j],
                                          event['source_power'],
                                          event['target_power'], size)
            elif op == 'contract':
                gaps = tuple(tuple(encoded_integer(x) for x in gap)
                             for gap in event['gaps'])
                record = _Contraction.from_gaps(gaps, emitted, len(steps))
                steps.append(record)
                contractions.append(record)
                emission_starts.append(emitted)
                emitted += record.emitted
                gap_count += len(gaps)
                max_gap_count = max(max_gap_count, len(gaps))
                size -= record.emitted
                rows = [[record.forward(x)[0] for x in row[:4]] + [row[4]]
                        for row in rows]
            elif op == 'truncate':
                i = encoded_integer(event['index'])
                cut = encoded_integer(event['new_size'])
                a, b, c, _, sign = rows[i]
                steps.append(_Truncation(cut, c - a,
                                         a + size - 1 if sign == -1 else None))
                removed = size - cut
                if cut == c:
                    rows.pop(i)
                elif sign == 1:
                    rows[i] = [a, b - removed, c, cut - 1, 1]
                else:
                    rows[i] = [a + removed, b, c, cut - 1, -1]
                size = cut
            else:
                raise ArithmeticError('unknown verified event')
        if size or rows or emitted != encoded_integer(proof['orbit_count']):
            raise ArithmeticError('index compilation did not finish')
        minima = _minimum_ranges(contractions, emitted, check)
        return cls(initial_size, emitted, tuple(steps), tuple(contractions),
                   tuple(emission_starts), len(proof['operations']), gap_count,
                   max_gap_count, *minima)

    @property
    def statistics(self):
        return dict(source_events=self._event_count, point_steps=len(self._steps),
                    contractions=len(self._contractions), gap_records=self._gap_count,
                    maximum_gaps=self._max_gap_count,
                    truncations=len(self._steps) - len(self._contractions),
                    minimum_intervals=len(self._minimum_intervals),
                    minimum_inverse_steps=self._minimum_inverse_steps)

    @property
    def minimum_intervals(self):
        """Canonical sorted, disjoint half-open intervals of all orbit minima."""
        return self._minimum_intervals

    def _point(self, point):
        point = _number(point, 'point')
        if point >= self.size:
            raise ValueError('point must lie inside the original universe')
        return point

    def _original(self, point, stop, check):
        used = 0
        for contraction in reversed(self._contractions):
            if contraction.position >= stop:
                continue
            _poll(check)
            point = contraction.backward(point)
            used += 1
        return point, used

    def locate(self, point, check=None):
        """Return a canonical minimum and a trace-dependent binary ordinal."""
        _poll(check)
        point = self._point(point)
        for step_number, step in enumerate(self._steps, 1):
            _poll(check)
            if isinstance(step, _Truncation):
                point = step.forward(point)
            else:
                surviving, ordinal = step.forward(point)
                if ordinal is not None:
                    original, used = self._original(point, step.position, check)
                    return OrbitLocation(original, ordinal, step_number, used)
                point = surviving
        raise ArithmeticError('a verified complete index failed to emit a point')

    def representative(self, point, check=None):
        return self.locate(point, check=check).representative

    def same_orbit(self, first, second, check=None):
        _poll(check)
        first, second = self._point(first), self._point(second)
        return (first == second or self.representative(first, check=check)
                == self.representative(second, check=check))

    def select(self, ordinal, check=None):
        """Select a minimum representative by trace emission ordinal.

        No loop depends on the ordinal's numeric value or the orbit count.
        The order of selected minima can differ between valid traces.
        """
        _poll(check)
        ordinal = _number(ordinal, 'ordinal')
        if ordinal >= self.count:
            raise ValueError('ordinal must lie below the orbit count')
        i = bisect_right(self._emission_starts, ordinal) - 1
        contraction = self._contractions[i]
        point = contraction.emitted_point(ordinal)
        return self._original(point, contraction.position, check)[0]

    def minimum_rank(self, representative, check=None):
        """Return the rank of a minimum in the sorted canonical minimum set.

        Reject points that are not minima.  This performs only interval binary
        search, and does not run a point through the reduction program.
        """
        _poll(check)
        representative = self._point(representative)
        i = bisect_right(self._minimum_starts, representative) - 1
        if i < 0 or representative >= self._minimum_intervals[i][1]:
            raise ValueError('the supplied point is not an orbit minimum')
        return self._minimum_prefix[i] + representative - self._minimum_starts[i]

    def orbit_rank(self, point, check=None):
        """Return the source-canonical sorted-minimum rank of a point's orbit."""
        return self.minimum_rank(self.representative(point, check=check), check=check)

    def select_minimum(self, rank, check=None):
        """Select the rank-th smallest original orbit minimum by binary search."""
        _poll(check)
        rank = _number(rank, 'rank')
        if rank >= self.count:
            raise ValueError('rank must lie below the orbit count')
        i = bisect_right(self._minimum_prefix, rank) - 1
        return self._minimum_starts[i] + rank - self._minimum_prefix[i]


def prepare_orbit_index(size, pairings, *, max_cycles=None,
                        periodic_rule='fine_wilf', check=None):
    """Discover one trace, then independently verify and compile it.

    Return ``(index, result)``; index is None when discovery is incomplete.
    max_cycles controls discovery only, just as in weighted trace reuse.
    Verification and compilation use cooperative cancellation.
    """
    from fastunknot.interval_orbits import count_orbits
    pairs = list(pairings)
    result = count_orbits(size, pairs, max_cycles=max_cycles,
                          periodic_rule=periodic_rule, check=check,
                          record_certificate=True)
    if not result.complete:
        return None, result
    index = OrbitIndex.from_certificate(size, pairs, result.certificate, check=check)
    return index, result
