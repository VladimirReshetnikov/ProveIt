"""Exact incidence histograms for marked interval-pseudogroup orbits.

Each port is a supplied union of half-open integer intervals. ``histogram[m]``
counts the original orbits meeting exactly the ports whose bits occur in m;
``histogram[0]`` includes every wholly unmarked orbit. Binary multiplicities are
never expanded. The algorithm uses at most 2**r classical AHT orbit queries
and a Boolean-lattice Moebius transform for r ports.

These counts preserve set incidence. They do not encode cyclic order, full
attaching maps, individual component identities, or knot recognition verdicts.
"""

from .integer_codec import encoded_integer
from .interval_orbits import analyze_orbits
from .interval_orbit_verify import verify_orbit_certificate
from .normal_components import cone_pairings


class _InvalidIncidence(ValueError):
    pass


def _poll(check):
    if check is not None:
        check()


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _InvalidIncidence("Expected an integer or hexadecimal string") from exc


def _prepare(size, ports, max_ports, check):
    size, max_ports = _integer(size), _integer(max_ports)
    if size < 0 or max_ports < 0:
        raise _InvalidIncidence("Negative universe or port allowance")
    if not isinstance(ports, (list, tuple)) or len(ports) > max_ports:
        raise _InvalidIncidence("Port list exceeds its explicit allowance")
    normalized = []
    for port in ports:
        _poll(check)
        if not isinstance(port, (list, tuple)):
            raise _InvalidIncidence("A port must be a list of intervals")
        intervals = []
        for interval in port:
            _poll(check)
            if not isinstance(interval, (list, tuple)) or len(interval) != 2:
                raise _InvalidIncidence("An interval needs two endpoints")
            lo, hi = map(_integer, interval)
            if not 0 <= lo <= hi <= size:
                raise _InvalidIncidence("A marked interval leaves the universe")
            if lo < hi:
                intervals.append([lo, hi])
        merged = []
        for lo, hi in sorted(intervals):
            if merged and lo <= merged[-1][1]:
                merged[-1][1] = max(merged[-1][1], hi)
            else:
                merged.append([lo, hi])
        normalized.append(merged)
    return size, normalized


def _marked_union(ports, mask):
    return [interval for bit, port in enumerate(ports) if mask & (1 << bit)
            for interval in port]


def _histogram(count, touched, port_count, check):
    """Invert G(U)=count-F(complement U)=sum_{T subset U} histogram[T]."""
    full = (1 << port_count) - 1
    result = [count - touched[full ^ mask] for mask in range(full + 1)]
    for bit in range(port_count):
        step = 1 << bit
        for mask in range(full + 1):
            _poll(check)
            if mask & step:
                result[mask] -= result[mask ^ step]
    if any(value < 0 for value in result) or sum(result) != count:
        raise ArithmeticError("Orbit counts violate incidence identities")
    return result


def analyze_port_incidence(size, pairings, ports, *, record_trace=False,
                           max_ports=12, max_cycles=None, check=None):
    """Compute the complete Boolean port-incidence histogram of the orbits.

    ``ports[i]`` is a list of half-open intervals. Port order determines the
    bit order in histogram indices, starting at bit zero. Each nonempty port
    union is coned to one class; from C original and C' coned classes its
    touched-orbit count is C-C'+1. Empty unions touch no orbit.

    The default limit of 12 ports bounds this exponential *port* enumeration;
    it is explicit and may be changed by callers. ``max_cycles`` applies to
    each orbit query. Use ``check`` for a cooperative whole-operation deadline.
    Limits and interruptions raise exceptions and never return a partial
    histogram as a completed answer.
    """
    if type(record_trace) is not bool:
        raise ValueError("record_trace must be boolean")
    _poll(check)
    size, ports = _prepare(size, ports, max_ports, check)
    r, slots = len(ports), 1 << len(ports)
    baseline = analyze_orbits(size, pairings, record_trace=record_trace,
                              max_cycles=max_cycles, check=check)
    count = baseline["orbit_count"]
    touched = [0] * slots
    queries = [None] * slots if record_trace else None
    if record_trace:
        queries[0] = baseline["certificate"]
    query_count, cycles = 1, baseline["stats"]["cycles"]
    for mask in range(1, slots):
        _poll(check)
        coned, nonempty = cone_pairings(size, pairings, _marked_union(ports, mask),
                                       check=check)
        if not nonempty:
            continue
        reply = analyze_orbits(size, coned, record_trace=record_trace,
                               max_cycles=max_cycles, check=check)
        touched[mask] = count - reply["orbit_count"] + 1
        query_count += 1
        cycles += reply["stats"]["cycles"]
        if record_trace:
            queries[mask] = reply["certificate"]
    histogram = _histogram(count, touched, r, check)
    result = {"orbit_count": count, "port_count": r, "histogram": histogram,
              "touched_counts": touched,
              "stats": {"orbit_queries": query_count, "orbit_cycles": cycles,
                        "histogram_slots": slots,
                        "marked_intervals": sum(map(len, ports))}}
    if record_trace:
        result["certificate"] = {
            "version": 1, "size": size, "ports": ports,
            "orbit_count": count, "histogram": histogram, "queries": queries}
    return result


def verify_port_incidence_certificate(size, pairings, ports, certificate, *,
                                       max_ports=12, check=None):
    """Verify marked input, every orbit trace, and the exact incidence histogram.

    No calls to the orbit producer occur. The same deterministic coning
    construction is used to bind each trace to its derived interval system;
    the orbit counts are checked by the separate local-replay verifier.
    Invalid data returns False; callback exceptions propagate.
    """
    try:
        return _verify(size, pairings, ports, certificate, max_ports, check)
    except _InvalidIncidence:
        return False


def _verify(size, pairings, ports, certificate, max_ports, check):
    _poll(check)
    size, ports = _prepare(size, ports, max_ports, check)
    if not isinstance(certificate, dict):
        raise _InvalidIncidence("Missing incidence certificate")
    if _integer(certificate.get("version")) != 1:
        raise _InvalidIncidence("Unknown incidence certificate version")
    if _integer(certificate.get("size")) != size:
        raise _InvalidIncidence("Wrong certificate universe")
    _, certified_ports = _prepare(size, certificate.get("ports"), max_ports, check)
    if certified_ports != ports:
        raise _InvalidIncidence("Certificate marks do not match the supplied ports")
    slots = 1 << len(ports)
    queries, histogram = certificate.get("queries"), certificate.get("histogram")
    if not isinstance(queries, list) or len(queries) != slots:
        raise _InvalidIncidence("Wrong list of coned orbit certificates")
    if not isinstance(histogram, list) or len(histogram) != slots:
        raise _InvalidIncidence("Wrong incidence histogram length")
    if not verify_orbit_certificate(size, pairings, queries[0], check=check):
        return False
    count = _integer(queries[0]["orbit_count"])
    if _integer(certificate.get("orbit_count")) != count:
        return False
    touched = [0] * slots
    for mask in range(1, slots):
        _poll(check)
        coned, nonempty = cone_pairings(size, pairings, _marked_union(ports, mask),
                                       check=check)
        if not nonempty:
            if queries[mask] is not None:
                return False
            continue
        if not verify_orbit_certificate(size, coned, queries[mask], check=check):
            return False
        touched[mask] = count - _integer(queries[mask]["orbit_count"]) + 1
        if not 0 <= touched[mask] <= count:
            return False
    # Verify the *forward* subset sums of the claimed histogram, rather than
    # rerunning the producer's inverse Moebius transform.  This has r*2**r
    # additions; enumerating all subsets of every mask would cost 3**r.
    full = slots - 1
    claimed = [_integer(value) for value in histogram]
    if any(value < 0 for value in claimed) or sum(claimed) != count:
        return False
    sums = list(claimed)
    width = 1
    while width < slots:
        for block in range(0, slots, 2 * width):
            for local in range(width):
                _poll(check)
                sums[block + width + local] += sums[block + local]
        width *= 2
    return all(sums[mask] == count - touched[full ^ mask] for mask in range(slots))
