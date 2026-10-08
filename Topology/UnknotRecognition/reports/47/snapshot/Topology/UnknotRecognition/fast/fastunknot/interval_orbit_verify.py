"""Independent replay checker for interval-pseudogroup orbit certificates.

The checker knows only the local orbit-preserving relations of the
Agol--Hass--Thurston algorithm.  It does not import the producer or rerun its
scheduler.  Its conclusion concerns the supplied interval system, not a knot.
Intervals contain integer points and have inclusive, zero-based endpoints.
"""

from math import gcd
import re


class _InvalidCertificate(ValueError):
    """A local witness did not satisfy its mathematical preconditions."""


def _integer(value):
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"[+-]?0[xX][0-9a-fA-F]+", value):
        return int(value, 16)
    raise _InvalidCertificate("Expected an integer or signed hexadecimal string")


def _row(raw, size):
    if isinstance(raw, (tuple, list)):
        if len(raw) != 5:
            raise _InvalidCertificate("A pairing needs five entries")
        values = list(raw)
    elif all(hasattr(raw, name) for name in ("a", "b", "c", "d", "sign")):
        values = [getattr(raw, name) for name in ("a", "b", "c", "d", "sign")]
    else:
        raise _InvalidCertificate("Unsupported pairing representation")
    a, b, c, d, sign = map(_integer, values)
    if sign not in (-1, 1):
        raise _InvalidCertificate("A pairing sign must be +1 or -1")
    if not (0 <= a <= b < size and 0 <= c <= d < size):
        raise _InvalidCertificate("Pairing outside its interval universe")
    if b - a != d - c:
        raise _InvalidCertificate("Pairing widths differ")
    if c < a:
        a, b, c, d = c, d, a, b
    return [a, b, c, d, sign]


def _public_pairings(size, pairings):
    if not isinstance(pairings, (tuple, list)):
        raise _InvalidCertificate("Pairings must be an explicit list or tuple")
    result = []
    for raw in pairings:
        if not isinstance(raw, dict) or set(raw) != {"start", "stop", "sign", "offset"}:
            raise _InvalidCertificate("Invalid public pairing schema")
        start, stop, sign, offset = (_integer(raw[name]) for name in
                                    ("start", "stop", "sign", "offset"))
        if sign not in (-1, 1) or not 0 <= start <= stop <= size:
            raise _InvalidCertificate("Invalid public pairing source")
        if start == stop:
            continue
        images = sorted((sign * start + offset, sign * (stop - 1) + offset))
        result.append(_row([start, stop - 1, *images, sign], size))
    return result


def _index(value, pairs):
    value = _integer(value)
    if not 0 <= value < len(pairs):
        raise _InvalidCertificate("Pairing index outside the current list")
    return value


def _gaps(size, pairs):
    """Compute the complement of all domains and ranges, without expansion."""
    intervals = sorted((lo, hi) for a, b, c, d, _ in pairs
                       for lo, hi in ((a, b), (c, d)))
    result = []
    first_free = 0
    for lo, hi in intervals:
        if first_free < lo:
            result.append([first_free, lo - 1])
        first_free = max(first_free, hi + 1)
    if first_free < size:
        result.append([first_free, size - 1])
    return result


def _inverse_image(interval, pairing, power):
    """Certify a power of one partial inverse and return its affine map.

    The returned pair (epsilon, offset) is the map on original points.
    Checking only the first and last intermediate intervals suffices: a
    positive translation moves them monotonically through one range.
    """
    power = _integer(power)
    if power < 0:
        raise _InvalidCertificate("Negative inverse power")
    lo, hi = interval
    a, b, c, d, sign = pairing
    if power == 0:
        return 1, 0
    if not (c <= lo <= hi <= d):
        raise _InvalidCertificate("Partial inverse is undefined")
    if sign == -1:
        if power != 1 or b >= c:
            raise _InvalidCertificate("Reflection transmitter must be trimmed")
        return -1, a + d
    distance = c - a
    if distance <= 0:
        raise _InvalidCertificate("Translation transmitter is the identity")
    if lo - (power - 1) * distance < c:
        raise _InvalidCertificate("Inverse power crosses the range boundary")
    return 1, -power * distance


def _transmitted_row(transmitter, target, source_power, target_power, size):
    if _integer(target_power) < 1:
        raise _InvalidCertificate("Transmission must move the target range")
    a, b, c, d, sign = target
    left_eps, left_off = _inverse_image((a, b), transmitter, source_power)
    right_eps, right_off = _inverse_image((c, d), transmitter, target_power)
    source = sorted((left_eps * a + left_off, left_eps * b + left_off))
    image = sorted((right_eps * c + right_off, right_eps * d + right_off))
    return _row([*source, *image, left_eps * sign * right_eps], size)


def verify_orbit_certificate(size, pairings, certificate, check=None):
    """Return whether a complete local-reduction trace certifies an orbit count.

    ``pairings`` uses the public half-open schema of ``interval_orbits``:
    dictionaries containing ``start,stop,sign,offset``. The starting list in ``certificate``
    must equal the normalized caller-supplied list, including its order.
    Invalid data returns ``False``.  Exceptions from the cooperative ``check``
    callback propagate; interruption is never converted into verification.

    A certificate is not an untrusted-input containment mechanism.  Work is
    polynomial in the supplied trace and integer bit lengths, and callers may
    impose their own serialized-size and deadline limits.
    """
    try:
        return _verify(size, pairings, certificate, check)
    except _InvalidCertificate:
        return False


def _verify(size, pairings, certificate, check):
    if check is not None:
        check()
    size = _integer(size)
    if size < 0 or not isinstance(certificate, dict):
        raise _InvalidCertificate("Invalid universe or certificate")
    if _integer(certificate.get("version")) != 1:
        raise _InvalidCertificate("Unsupported certificate version")
    if _integer(certificate.get("size")) != size:
        raise _InvalidCertificate("Certificate universe differs from input")
    current = _public_pairings(size, pairings)
    bound_rows = certificate.get("pairings")
    if not isinstance(bound_rows, list):
        raise _InvalidCertificate("Missing starting pairings")
    # Validate before equality: bool and int compare equal in Python.
    supplied = [_row(raw, size) for raw in bound_rows]
    decoded_rows = [[_integer(value) for value in raw] for raw in bound_rows]
    if supplied != current or decoded_rows != supplied:
        raise _InvalidCertificate("Starting pairings are not canonical input")
    operations = certificate.get("operations")
    if not isinstance(operations, list):
        raise _InvalidCertificate("Missing operation trace")
    claimed = _integer(certificate.get("orbit_count"))
    if claimed < 0 or claimed > size:
        raise _InvalidCertificate("Impossible orbit count")
    removed_orbits = 0

    for event in operations:
        if check is not None:
            check()
        if not isinstance(event, dict):
            raise _InvalidCertificate("Invalid event")
        operation = event.get("op")

        if operation == "delete":
            i = _index(event.get("index"), current)
            a, b, c, d, sign = current[i]
            if a != c or (sign != 1 and a != b):
                raise _InvalidCertificate("Only an identity may be deleted")
            del current[i]

        elif operation == "contract":
            expected = _gaps(size, current)
            actual = event.get("gaps")
            if not isinstance(actual, list) or not expected:
                raise _InvalidCertificate("Contraction needs static intervals")
            decoded_gaps = []
            for gap in actual:
                if not isinstance(gap, list) or len(gap) != 2:
                    raise _InvalidCertificate("Invalid contraction interval")
                decoded_gaps.append([_integer(endpoint) for endpoint in gap])
            if decoded_gaps != expected:
                raise _InvalidCertificate("Contraction gaps are not static")
            actual = decoded_gaps

            def shifted(point):
                return point - sum(hi - lo + 1 for lo, hi in actual if hi < point)

            decrease = sum(hi - lo + 1 for lo, hi in actual)
            current = [[shifted(a), shifted(b), shifted(c), shifted(d), sign]
                       for a, b, c, d, sign in current]
            size -= decrease
            removed_orbits += decrease

        elif operation == "trim":
            i = _index(event.get("index"), current)
            a, b, c, d, sign = current[i]
            if sign != -1 or b < c:
                raise _InvalidCertificate("Only an overlapping reflection trims")
            last_left = (a + d - 1) // 2
            if last_left < a:
                raise _InvalidCertificate("An identity must use deletion")
            current[i] = _row([a, last_left, a + d - last_left, d, -1], size)

        elif operation == "merge":
            i = _index(event.get("left"), current)
            j = _index(event.get("right"), current)
            if i == j:
                raise _InvalidCertificate("A merger needs distinct pairings")
            a, b, c, d, sign = current[i]
            aa, bb, cc, dd, ss = current[j]
            t, u = c - a, cc - aa
            if not (sign == ss == 1 and 0 < t <= b - a + 1
                    and 0 < u <= bb - aa + 1):
                raise _InvalidCertificate("Merger operands are not periodic")
            if min(d, dd) - max(a, aa) + 1 < t + u:
                raise _InvalidCertificate("Periodic overlap is insufficient")
            lo, hi = min(a, aa), max(d, dd)
            period = gcd(t, u)
            replacement = _row([lo, hi - period, lo + period, hi, 1], size)
            # The producer retains the replacement at the smaller index.
            low, high = sorted((i, j))
            current[low] = replacement
            del current[high]

        elif operation == "transmit":
            i = _index(event.get("transmitter"), current)
            j = _index(event.get("target"), current)
            if i == j:
                raise _InvalidCertificate("A pairing cannot transmit itself")
            current[j] = _transmitted_row(
                current[i], current[j], event.get("source_power"),
                event.get("target_power"), size)

        elif operation == "truncate":
            i = _index(event.get("index"), current)
            new_size = _integer(event.get("new_size"))
            a, b, c, d, sign = current[i]
            if not (0 <= new_size < size and d == size - 1 and c <= new_size):
                raise _InvalidCertificate("Invalid suffix for truncation")
            if sign == 1 and c <= a:
                raise _InvalidCertificate("An identity has no earlier orbit representative")
            if sign == -1 and b >= c:
                raise _InvalidCertificate("Reflection truncation needs trimming")
            for j, (aa, bb, cc, dd, _) in enumerate(current):
                if j != i and (bb >= new_size or dd >= new_size):
                    raise _InvalidCertificate("Suffix meets another pairing")
            if new_size == c:
                del current[i]
            else:
                removed = size - new_size
                if sign == 1:
                    current[i] = _row([a, b - removed, c, new_size - 1, 1],
                                      new_size)
                else:
                    current[i] = _row([a + removed, b, c, new_size - 1, -1],
                                      new_size)
            size = new_size

        else:
            raise _InvalidCertificate("Unknown orbit-reduction operation")

    return size == 0 and not current and removed_orbits == claimed
