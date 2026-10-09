"""Independent source-bound replay of compressed orbit transversals.

This checker imports neither the transversal producer nor the orbit scheduler.
It first checks the supplied source and all AHT moves using the maintained
independent orbit checker.  It then reverses those moves: a contraction puts
selected gaps back, while a truncation restores an unselected suffix.  This
differs from the producer's forward bookkeeping of surviving original labels.
"""

from bisect import bisect_right

from .integer_codec import encoded_integer
from .interval_orbit_verify import verify_orbit_certificate


class _InvalidTransversal(ValueError):
    pass


def _number(value):
    try:
        return encoded_integer(value)
    except ValueError as exc:
        raise _InvalidTransversal('expected an integer or hexadecimal string') from exc


def _union(intervals, check):
    answer = []
    for lo, hi in sorted(intervals):
        check()
        if lo >= hi:
            raise _InvalidTransversal('empty or reversed selector interval')
        if answer and lo <= answer[-1][1]:
            answer[-1] = (answer[-1][0], max(hi, answer[-1][1]))
        else:
            answer.append((lo, hi))
    return answer


def _reverse_selector(size, proof, check):
    """Lift a selected set backwards through contractions and truncations."""
    history, current = [], size
    for event in proof['operations']:
        check()
        operation = event['op']
        if operation == 'contract':
            gaps = [(_number(lo), _number(hi) + 1) for lo, hi in event['gaps']]
            decrease = sum(hi - lo for lo, hi in gaps)
            history.append((current, gaps))
            current -= decrease
        elif operation == 'truncate':
            history.append((current, None))
            current = _number(event['new_size'])
        elif operation not in ('delete', 'trim', 'merge', 'transmit'):
            # Least original representatives rely on increasing survivor
            # coordinates. Orbit-count validity alone does not imply this.
            raise _InvalidTransversal('the least selector requires a monotone trace')
    if current:
        raise _InvalidTransversal('the orbit trace is incomplete')
    selected = []
    for restored_size, gaps in reversed(history):
        check()
        if gaps is not None:
            anchors, prefix = [], [0]
            for lo, hi in gaps:
                check()
                anchors.append(lo - prefix[-1])
                prefix.append(prefix[-1] + hi - lo)

            def restore(point):
                return point + prefix[bisect_right(anchors, point)]

            # A selected interval's convex hull only adds reinserted gap
            # points, all of which are selected separately below anyway.
            lifted = []
            for lo, hi in selected:
                check()
                lifted.append((restore(lo), restore(hi - 1) + 1))
            selected = _union(lifted + gaps, check)
        # Restoring a truncated suffix adds no selected points.
        current = restored_size
    if current != size:
        raise _InvalidTransversal('source universe reconstruction failed')
    return selected


def _verify(size, pairings, certificate, check):
    check()
    size = _number(size)
    if size < 0 or type(certificate) is not dict:
        raise _InvalidTransversal('invalid source or certificate')
    if certificate.get('schema') != 'interval-orbit-transversal-v1':
        raise _InvalidTransversal('unsupported transversal schema')
    if _number(certificate.get('size')) != size:
        raise _InvalidTransversal('source universe mismatch')
    proof = certificate.get('orbit_proof')
    if not verify_orbit_certificate(size, pairings, proof, check=check):
        raise _InvalidTransversal('source-bound orbit replay failed')
    raw = certificate.get('representative_intervals')
    if type(raw) is not list:
        raise _InvalidTransversal('missing representative intervals')
    proposed = []
    previous_stop = -1
    for record in raw:
        check()
        if type(record) is not list or len(record) != 2:
            raise _InvalidTransversal('invalid representative interval')
        lo, hi = map(_number, record)
        if not 0 <= lo < hi <= size or lo <= previous_stop:
            raise _InvalidTransversal('representative intervals must be canonical')
        proposed.append((lo, hi))
        previous_stop = hi
    if proposed != _reverse_selector(size, proof, check):
        raise _InvalidTransversal('the claimed source transversal is incorrect')
    count = sum(hi - lo for lo, hi in proposed)
    if (count != _number(proof['orbit_count'])
            or count != _number(certificate.get('orbit_count'))):
        raise _InvalidTransversal('transversal cardinality mismatch')
    check()
    return True


def verify_orbit_transversal_certificate(size, pairings, certificate, *, check=None):
    """Check the exact source trace and the canonical least representative set.

    Malformed data returns False.  Callback exceptions propagate, including
    those raised by false-valued callable objects.  Verification cost includes
    source replay and is polynomial in its explicit trace and integer bits.
    Global reflection events are rejected: an arbitrary orbit-count proof
    need not preserve the source order needed for least representatives.
    """
    poll = check if check is not None else lambda: None
    try:
        return _verify(size, list(pairings), certificate, poll)
    except _InvalidTransversal:
        return False
