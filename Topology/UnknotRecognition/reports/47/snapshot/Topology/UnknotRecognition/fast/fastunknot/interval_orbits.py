"""Exact orbit counts for binary-encoded partial interval isometries.

This is an independent implementation of the classical Agol--Hass--Thurston
orbit-counting algorithm (2004, Section 4).  It accepts arbitrary partial
translations and reflections, not just total maps on a cyclic fibre.  No
interval is expanded into its integer points.

The public pairing schema is ``{start, stop, sign, offset}``, representing
``x -> sign*x + offset`` on the half-open integer interval ``[start, stop)``.
All source and image points must lie in ``[0, size)``.  Integers can use the
project's exact hexadecimal JSON transport.  Empty source intervals are
validated and ignored.  A recorded trace is independently checked by
``interval_orbit_verify.verify_orbit_certificate``.

The AHT theorem gives polynomial time in the number of pairings and the bit
length of ``size``.  It does not bound a normal-surface search or establish an
end-to-end quasipolynomial unknot recognizer.
"""

from __future__ import annotations

from bisect import bisect_right
from dataclasses import dataclass
from math import gcd

from .integer_codec import encoded_integer


class OrbitLimitExceeded(RuntimeError):
    """An explicit orbit-analysis allowance was exhausted; no count exists."""


@dataclass(frozen=True, slots=True)
class _Pairing:
    """Inclusive, zero-based equal-length intervals, with ``a <= c``."""

    a: int
    b: int
    c: int
    d: int
    sign: int

    @property
    def width(self):
        return self.b - self.a + 1

    @property
    def period(self):
        return self.c - self.a

    @property
    def identity(self):
        return self.a == self.c and (self.sign == 1 or self.width == 1)

    @property
    def periodic(self):
        return self.sign == 1 and 0 < self.period <= self.width

    def record(self):
        return [self.a, self.b, self.c, self.d, self.sign]


def _poll(check):
    if check is not None:
        check()


def _integer(value, name):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer or hexadecimal string") from exc


def _canonical(a, b, c, d, sign):
    if a > c:
        a, b, c, d = c, d, a, b
    return _Pairing(a, b, c, d, sign)


def _prepare(size, pairings, check):
    size = _integer(size, "size")
    if size < 0:
        raise ValueError("size must be nonnegative")
    if not isinstance(pairings, (list, tuple)):
        raise ValueError("pairings must be an explicit list or tuple")
    result = []
    for index, raw in enumerate(pairings):
        _poll(check)
        if not isinstance(raw, dict) or set(raw) != {"start", "stop", "sign", "offset"}:
            raise ValueError(f"pairing {index} requires start, stop, sign and offset")
        start, stop, sign, offset = (
            _integer(raw[key], f"pairing {index}.{key}")
            for key in ("start", "stop", "sign", "offset")
        )
        if sign not in (-1, 1):
            raise ValueError(f"pairing {index} sign must be +1 or -1")
        if not 0 <= start <= stop <= size:
            raise ValueError(f"pairing {index} has a source outside the universe")
        if start == stop:
            continue
        end = stop - 1
        first, last = sign * start + offset, sign * end + offset
        c, d = min(first, last), max(first, last)
        if not 0 <= c <= d < size:
            raise ValueError(f"pairing {index} has an image outside the universe")
        result.append(_canonical(start, end, c, d, sign))
    return size, result


def _static_gaps(size, pairings, check):
    intervals = sorted((lo, hi) for p in pairings
                       for lo, hi in ((p.a, p.b), (p.c, p.d)))
    end = 0
    gaps = []
    for lo, hi in intervals:
        _poll(check)
        if lo > end:
            gaps.append([end, lo - 1])
        end = max(end, hi + 1)
    if end < size:
        gaps.append([end, size - 1])
    return gaps


def _contract(pairings, gaps, check):
    """Delete all supplied static intervals by an order-preserving relabeling."""
    ends = []
    removed = [0]
    for lo, hi in gaps:
        _poll(check)
        ends.append(hi)
        removed.append(removed[-1] + hi - lo + 1)

    def image(x):
        return x - removed[bisect_right(ends, x)]

    result = []
    for p in pairings:
        _poll(check)
        result.append(_Pairing(image(p.a), image(p.b), image(p.c), image(p.d), p.sign))
    return result, removed[-1]


def _merge_pair(pairings, check):
    """Return the first legal periodic merger, or None.  Adjacency is legal."""
    for i, p in enumerate(pairings):
        _poll(check)
        if not p.periodic:
            continue
        for j in range(i + 1, len(pairings)):
            _poll(check)
            q = pairings[j]
            if q.periodic and min(p.d, q.d) - max(p.a, q.a) + 1 >= p.period + q.period:
                period = gcd(p.period, q.period)
                left, right = min(p.a, q.a), max(p.d, q.d)
                merged = _Pairing(left, right - period, left + period, right, 1)
                return i, j, merged
    return None


def _transmit(transmitter, target):
    """Apply the largest legal inverse power to each eligible entire interval."""
    p, q = transmitter, target
    if p.sign == 1:
        period = p.period
        r = (q.c - p.c) // period + 1
        c, d = q.c - r * period, q.d - r * period
        if p.c <= q.a and q.b <= p.d:
            s = (q.a - p.c) // period + 1
            a, b = q.a - s * period, q.b - s * period
        else:
            s = 0
            a, b = q.a, q.b
        sign = q.sign
    else:
        r = 1
        reflection = p.a + p.d
        c, d = reflection - q.d, reflection - q.c
        if p.c <= q.a and q.b <= p.d:
            s = 1
            a, b = reflection - q.b, reflection - q.a
            sign = q.sign
        else:
            s = 0
            a, b = q.a, q.b
            sign = -q.sign
    return _canonical(a, b, c, d, sign), s, r


def analyze_orbits(size, pairings, *, record_trace=False, check=None, max_cycles=None):
    """Count partial-isometry orbits with exact work statistics and optional proof.

    ``check`` is called cooperatively throughout the algorithm; its exceptions
    propagate. ``max_cycles`` is an optional explicit scheduler-cycle cap. An
    exhausted cap raises :class:`OrbitLimitExceeded`, never a partial count.
    ``stats`` records algorithmic operations, not estimated runtime or memory.
    The optional certificate uses inclusive zero-based internal intervals.
    """
    if type(record_trace) is not bool:
        raise ValueError("record_trace must be boolean")
    if max_cycles is not None:
        max_cycles = _integer(max_cycles, "max_cycles")
        if max_cycles < 0:
            raise ValueError("max_cycles must be nonnegative")
    initial_size, current = _prepare(size, pairings, check)
    size = initial_size
    initial = [p.record() for p in current] if record_trace else None
    operations = [] if record_trace else None
    stats = {"cycles": 0, "identities": 0, "contractions": 0,
             "contracted_points": 0, "trims": 0, "mergers": 0,
             "transmissions": 0, "truncations": 0,
             "truncated_points": 0, "max_pairings": len(current),
             "input_size_bits": initial_size.bit_length()}
    count = 0

    def record(op, **payload):
        if operations is not None:
            operations.append({"op": op, **payload})

    while size:
        _poll(check)
        if max_cycles is not None and stats["cycles"] >= max_cycles:
            raise OrbitLimitExceeded("interval-orbit cycle allowance exhausted")
        stats["cycles"] += 1

        # Step 1: identity pairings impose no relation beyond reflexivity.
        for i in range(len(current) - 1, -1, -1):
            _poll(check)
            if current[i].identity:
                record("delete", index=i)
                del current[i]
                stats["identities"] += 1

        # Step 2: all static points are singleton orbits. Contract by rank.
        gaps = _static_gaps(size, current, check)
        if gaps:
            record("contract", gaps=gaps)
            current, removed = _contract(current, gaps, check)
            size -= removed
            count += removed
            stats["contractions"] += len(gaps)
            stats["contracted_points"] += removed
        if not current:
            if size:
                raise ArithmeticError("static contraction left an uncovered universe")
            break

        # Step 3: remove the duplicated half of every overlapping reflection.
        for i, p in enumerate(current):
            _poll(check)
            if p.sign == -1 and p.b >= p.c:
                record("trim", index=i)
                middle_sum = p.a + p.d
                current[i] = _Pairing(p.a, (middle_sum - 1) // 2,
                                      middle_sum // 2 + 1, p.d, -1)
                stats["trims"] += 1

        # Step 4: exhaustive legal periodic mergers, retaining the full hull.
        while True:
            merge = _merge_pair(current, check)
            if merge is None:
                break
            i, j, p = merge
            record("merge", left=i, right=j)
            current[i] = p
            del current[j]
            stats["mergers"] += 1

        # Step 5: move every other range contained in the maximal range left.
        i = max(range(len(current)), key=lambda j: (
            current[j].d, -current[j].c, -current[j].a, -current[j].sign))
        p = current[i]
        if p.d != size - 1:
            raise ArithmeticError("maximal interval does not reach the universe end")
        for j in range(len(current)):
            _poll(check)
            if j == i:
                continue
            q = current[j]
            if p.c <= q.c and q.d <= p.d:
                changed, s, r = _transmit(p, q)
                record("transmit", transmitter=i, target=j,
                       source_power=s, target_power=r)
                current[j] = changed
                stats["transmissions"] += 1

        # Step 6: the remaining right-hand suffix meets this pairing alone.
        other_end = max((q.d for j, q in enumerate(current) if j != i), default=-1)
        new_size = max(p.c, other_end + 1)
        if new_size >= size:
            raise ArithmeticError("AHT transmission did not expose a nonempty suffix")
        record("truncate", index=i, new_size=new_size)
        removed = size - new_size
        if new_size == p.c:
            del current[i]
        elif p.sign == 1:
            current[i] = _Pairing(p.a, p.b - removed, p.c, new_size - 1, 1)
        else:
            current[i] = _Pairing(p.a + removed, p.b, p.c, new_size - 1, -1)
        size = new_size
        stats["truncations"] += 1
        stats["truncated_points"] += removed

    result = {"orbit_count": count, "stats": stats}
    if record_trace:
        result["certificate"] = {"version": 1, "size": initial_size,
                                 "pairings": initial, "orbit_count": count,
                                 "operations": operations}
    return result


def count_orbits(size, pairings, *, check=None, max_cycles=None):
    """Return only the exact orbit count; never enumerate represented points."""
    return analyze_orbits(size, pairings, check=check,
                          max_cycles=max_cycles)["orbit_count"]
