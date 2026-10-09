"""Schemas and coning geometry shared by sparse producer and verifier (MIT-0).

No orbit algorithm or sparse-reconstruction algorithm is imported here.
Pairings are inclusive; ports are half-open. Integers reject Python bools.
"""
from .integer_codec import encoded_integer


class InvalidSparse(ValueError):
    """Malformed sparse-incidence input or proof."""


def integer(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise InvalidSparse('expected an integer or hexadecimal string') from exc


def allowance(value, name):
    if value is not None and (type(value) is not int or value < 0):
        raise InvalidSparse(f'{name} must be a nonnegative integer or None')
    return value


def union(intervals, poll=lambda: None):
    merged = []
    for lo, hi in sorted(intervals):
        poll()
        if lo == hi:
            continue
        if merged and lo <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(hi, merged[-1][1]))
        else:
            merged.append((lo, hi))
    return tuple(merged)


def prepare(size, ports, max_ports, poll):
    size = integer(size)
    allowance(max_ports, 'max_ports')
    if size < 0 or not isinstance(ports, (list, tuple)):
        raise InvalidSparse('invalid universe or port container')
    if max_ports is not None and len(ports) > max_ports:
        raise InvalidSparse('port allowance exceeded')
    out = []
    for port in ports:
        poll()
        if not isinstance(port, (list, tuple)):
            raise InvalidSparse('each port is a list of half-open intervals')
        intervals = []
        for interval in port:
            poll()
            if not isinstance(interval, (list, tuple)) or len(interval) != 2:
                raise InvalidSparse('each interval has two endpoints')
            lo, hi = map(integer, interval)
            if not 0 <= lo <= hi <= size:
                raise InvalidSparse('marked interval outside the universe')
            intervals.append((lo, hi))
        out.append(union(intervals, poll))
    return size, tuple(out)


def selected_union(ports, mask, poll):
    intervals = []
    for bit, port in enumerate(ports):
        poll()
        if mask & (1 << bit):
            intervals.extend(port)
    return union(intervals, poll)


def cone_rows(intervals):
    if not intervals:
        return []
    hub = intervals[0][0]
    rows = []
    for lo, hi in intervals:
        if hi - lo > 1:
            rows.append([lo, hi - 2, lo + 1, hi - 1, 1])
        if lo != hub:
            rows.append([hub, hub, lo, lo, 1])
    return rows


def pairing_rows(size, pairings, poll):
    if not isinstance(pairings, (list, tuple)):
        raise InvalidSparse('pairings must be an explicit list or tuple')
    rows = []
    for pair in pairings:
        poll()
        if isinstance(pair, (list, tuple)) and len(pair) == 5:
            values = pair
        elif all(hasattr(pair, key) for key in ('a', 'b', 'c', 'd', 'reverse')):
            if type(pair.reverse) is not bool:
                raise InvalidSparse('reverse must be bool')
            values = [pair.a, pair.b, pair.c, pair.d, -1 if pair.reverse else 1]
        else:
            raise InvalidSparse('expected a pairing object or inclusive five-entry row')
        a, b, c, d, sign = map(integer, values)
        if (sign not in (-1, 1) or not 0 <= a <= b < size
                or not 0 <= c <= d < size or b - a != d - c):
            raise InvalidSparse('invalid interval pairing')
        if a > c:
            a, b, c, d = c, d, a, b
        rows.append([a, b, c, d, sign])
    return rows
