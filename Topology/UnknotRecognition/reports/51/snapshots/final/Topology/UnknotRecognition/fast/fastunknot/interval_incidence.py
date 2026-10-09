"""Exact component counts by incidence with supplied marked interval unions.

Based on report 47's coning identity and Boolean-lattice inversion (MIT-0).
Repeated unions share one orbit query and one certificate. The output still
has 2**r slots for r ports; this is not an attachment map or a knot verdict.
All orbit queries share one cycle budget. Interrupted runs publish no histogram.
"""
from .integer_codec import encoded_integer
from .interval_orbits import IntervalPairing, count_orbits
from .interval_orbit_verify import verify_orbit_certificate


class _InvalidIncidence(ValueError):
    pass


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _InvalidIncidence('expected an integer or hexadecimal string') from exc


def _union(intervals):
    merged = []
    for lo, hi in sorted(intervals):
        if lo == hi:
            continue
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    return tuple(merged)


def _prepare(size, ports, max_ports, check):
    size, max_ports = _integer(size), _integer(max_ports)
    if size < 0 or max_ports < 0:
        raise _InvalidIncidence('negative universe or port allowance')
    if not isinstance(ports, (list, tuple)) or len(ports) > max_ports:
        raise _InvalidIncidence('port list exceeds its explicit allowance')
    result = []
    for port in ports:
        check()
        if not isinstance(port, (list, tuple)):
            raise _InvalidIncidence('each port must contain half-open intervals')
        intervals = []
        for interval in port:
            check()
            if not isinstance(interval, (list, tuple)) or len(interval) != 2:
                raise _InvalidIncidence('an interval requires two endpoints')
            lo, hi = map(_integer, interval)
            if not 0 <= lo <= hi <= size:
                raise _InvalidIncidence('marked interval leaves the universe')
            intervals.append((lo, hi))
        result.append(_union(intervals))
    return size, tuple(result)


def _selected_union(ports, mask):
    return _union(interval for bit, port in enumerate(ports)
                  if mask & (1 << bit) for interval in port)


def _cone_rows(intervals):
    """Collapse a nonempty marked union using interval translations and a star."""
    hub = intervals[0][0]
    rows = []
    for lo, hi in intervals:
        if hi - lo > 1:
            rows.append([lo, hi - 2, lo + 1, hi - 1, 1])
        if lo != hub:
            rows.append([hub, hub, lo, lo, 1])
    return rows


def analyze_port_incidence(size, pairings, ports, *, max_ports=12, max_cycles=None,
                           record_certificate=False, check=None):
    """Count orbits meeting exactly each subset of the supplied ports.

    Ports are unions of half-open intervals; histogram bit i denotes port i.
    Empty ports, coincident ports, overlaps and unmarked components are allowed.
    COMPLETE results contain 2**len(ports) counts. INCONCLUSIVE results contain
    only status and work statistics. A total max_cycles allowance is shared by
    the baseline and all distinct coned-union queries. A callback controls a
    cooperative deadline, including union construction and subset inversion.

    Optional version-2 certificates store each distinct coned proof once and
    bind all masks through an index array. No normal-surface or knot provenance
    is implied. Use integer_codec.json_safe for serialized binary integers.
    """
    poll = check if check is not None else lambda: None
    poll()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    size, ports = _prepare(size, ports, max_ports, poll)
    pairs = list(pairings)
    stats = dict(orbit_queries=0, orbit_cycles=0, union_cache_hits=0,
                 empty_unions=0, histogram_slots=1 << len(ports))

    def query(extra):
        remaining = None if max_cycles is None else max_cycles - stats['orbit_cycles']
        result = count_orbits(size, pairs + extra, max_cycles=remaining,
                              check=poll, record_certificate=record_certificate)
        stats['orbit_queries'] += 1
        stats['orbit_cycles'] += result.cycles
        return result

    base = query([])
    if not base.complete:
        return dict(status='INCONCLUSIVE', stats=stats)
    touched = [0] * stats['histogram_slots']
    indices = [None] * len(touched) if record_certificate else None
    proofs = [] if record_certificate else None
    cache = {}
    for mask in range(1, len(touched)):
        poll()
        union = _selected_union(ports, mask)
        if not union:
            stats['empty_unions'] += 1
            continue
        if union in cache:
            value, index = cache[union]
            stats['union_cache_hits'] += 1
        else:
            extra = [IntervalPairing(a, b, c, d) for a, b, c, d, _ in _cone_rows(union)]
            reply = query(extra)
            if not reply.complete:
                return dict(status='INCONCLUSIVE', stats=stats)
            value, index = base.orbits - reply.orbits + 1, len(cache)
            if not 0 <= value <= base.orbits:
                raise ArithmeticError('coned count violates the touched-orbit identity')
            cache[union] = value, index
            if proofs is not None:
                proofs.append(reply.certificate)
        touched[mask] = value
        if indices is not None:
            indices[mask] = index
    full = len(touched) - 1
    histogram = [base.orbits - touched[full ^ mask] for mask in range(len(touched))]
    for bit in range(len(ports)):
        for mask in range(len(touched)):
            poll()
            if mask & (1 << bit):
                histogram[mask] -= histogram[mask ^ (1 << bit)]
    if any(value < 0 for value in histogram) or sum(histogram) != base.orbits:
        raise ArithmeticError('orbit counts violate incidence identities')
    result = dict(status='COMPLETE', orbit_count=base.orbits,
                  histogram=histogram, touched_counts=touched, stats=stats)
    if record_certificate:
        result['certificate'] = dict(version=2, size=size, ports=ports,
            orbit_count=base.orbits, histogram=histogram, base=base.certificate,
            proofs=proofs, query_indices=indices)
    poll()
    return result


def verify_port_incidence_certificate(size, pairings, ports, certificate, *,
                                       max_ports=12, check=None):
    """Replay each distinct count and verify forward subset sums independently.

    The verifier never calls the orbit producer or inverse transform. It shares
    only input normalization and the explicit coning construction, whose local
    count is certified by independent orbit replay. Invalid data returns False;
    callback exceptions propagate. Certificate work is bounded by its explicit
    size and the port allowance, not by the number of represented points.
    """
    try:
        return _verify(size, pairings, ports, certificate, max_ports,
                       check if check is not None else lambda: None)
    except _InvalidIncidence:
        return False


def _verify(size, pairings, ports, cert, max_ports, poll):
    poll()
    size, ports = _prepare(size, ports, max_ports, poll)
    if not isinstance(cert, dict) or _integer(cert.get('version')) != 2:
        return False
    if _integer(cert.get('size')) != size:
        return False
    _, bound_ports = _prepare(size, cert.get('ports'), max_ports, poll)
    if bound_ports != ports or not isinstance(pairings, (list, tuple)):
        return False
    slots = 1 << len(ports)
    indices, proofs, histogram = (cert.get(key) for key in
                                   ('query_indices', 'proofs', 'histogram'))
    if (not isinstance(indices, list) or len(indices) != slots
            or not isinstance(proofs, list) or len(proofs) >= slots
            or not isinstance(histogram, list) or len(histogram) != slots):
        return False
    if not verify_orbit_certificate(size, pairings, cert.get('base'), check=poll):
        return False
    count = _integer(cert['base']['orbit_count'])
    if _integer(cert.get('orbit_count')) != count or indices[0] is not None:
        return False
    touched, seen, cache = [0] * slots, set(), {}
    for mask in range(1, slots):
        poll()
        union = _selected_union(ports, mask)
        index = indices[mask]
        if not union:
            if index is not None:
                return False
            continue
        index = _integer(index)
        if not 0 <= index < len(proofs):
            return False
        if union not in cache:
            if index in seen:
                return False  # A proof cannot be rebound to a different union.
            coned = list(pairings) + _cone_rows(union)
            if not verify_orbit_certificate(size, coned, proofs[index], check=poll):
                return False
            value = count - _integer(proofs[index]['orbit_count']) + 1
            if not 0 <= value <= count:
                return False
            cache[union] = index, value
            seen.add(index)
        if index != cache[union][0]:
            return False
        touched[mask] = cache[union][1]
    if len(seen) != len(proofs):
        return False
    claimed = [_integer(value) for value in histogram]
    if any(value < 0 for value in claimed) or sum(claimed) != count:
        return False
    # Forward zeta transform differs from the producer's Moebius subtraction.
    sums = list(claimed)
    width = 1
    while width < slots:
        for block in range(0, slots, 2 * width):
            for local in range(width):
                poll()
                sums[block + width + local] += sums[block + local]
        width *= 2
    return all(sums[mask] == count - touched[(slots - 1) ^ mask]
               for mask in range(slots))
